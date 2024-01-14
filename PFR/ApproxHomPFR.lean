import PFR.HomPFR
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The approximate homomorphism form of PFR

Here we apply PFR to show that almost homomorphisms f from a 2-group to a 2-group often coincide with a (shifted) actual homomorphisms.  Here, approximate is in the sense that f(x+y)=f(x)+f(y) is true for a positive proportion of x,y.

## Main result

* `approx_hom_pfr` : If $f: G → G'$ is a map between finite abelian elementary 2-groups such that $f(x+y)=f(x)+f(y)$ for at least $|G|/K$ values, then then there is a homomorphism $\phi: G \to G'$ and a constant $c$ such that $f(x)=\phi(x)+c$ for a substantial set of values.

-/
open Pointwise Classical

variable {G : Type*} [AddCommGroup G] (A : Finset G)

/-- If $G$ is a group, and $A$ is a finite subset of $G$, the \emph{additive energy} $E(A)$ of $A$ is the number of quadruples $(a_1,a_2,a_3,a_4) \in A^4$ such that $a_1+a_2 = a_3+a_4$. -/
notation3:max "E[" A "]" => Finset.additiveEnergy A A

lemma nat_cauchy_schwartz {B : Type*} [Fintype B] (v w : B → ℕ) :
  (Finset.univ.sum (v * w))^2 ≤ Finset.univ.sum (v^2) * Finset.univ.sum (w^2) := by
  rify
  let x : EuclideanSpace ℝ B := fun i ↦ (v i : ℝ)
  let y : EuclideanSpace ℝ B := fun i ↦ (w i : ℝ)
  have := abs_real_inner_le_norm x y
  rw [PiLp.inner_apply, ((abs_eq (mul_nonneg (norm_nonneg x) (norm_nonneg y))).mpr
    (abs_eq_abs.mp rfl)).symm, ← sq_le_sq, mul_pow, EuclideanSpace.norm_eq,EuclideanSpace.norm_eq] at this
  rw [Real.sq_sqrt, Real.sq_sqrt] at this
  · simp only [IsROrC.norm_natCast] at this
    simp only [Real.sq_sqrt, Real.sq_sqrt, IsROrC.norm_natCast, Pi.mul_apply, Nat.cast_mul,
      Pi.pow_apply, Nat.cast_pow, ge_iff_le]
    exact this
  all_goals { apply Finset.sum_nonneg (fun i _ ↦ sq_nonneg _) }

lemma nat_cauchy_schwartz' {X : Type*} (B : Finset X) (v w : X → ℕ) :
  (B.sum (v * w))^2 ≤ B.sum (v^2) * B.sum (w^2) := by
  have := nat_cauchy_schwartz (fun b : B => v b) (fun b : B => w b)
  rwa [← (show Finset.univ.sum (fun b : B => (v * w) b) = B.sum (v * w) from Finset.sum_attach _ _),
    ← (show Finset.univ.sum (fun b : B => (v^2 : X → ℕ) b) = B.sum (v^2) from Finset.sum_attach _ _),
    ← (show Finset.univ.sum (fun b : B => (w^2 : X → ℕ) b) = B.sum (w^2) from Finset.sum_attach _ _)]

/--  If $G$ is a group, $A,B$ are finite subsets of $G$, then
$$ E(A) \geq \frac{|\{ (a,a') \in A \times A: a+a' \in B \}|^2}{|B|}.$$ -/
lemma cauchy_schwarz (A B : Finset G) :
  ((A ×ˢ A).filter (fun (a : G × G) => a.fst + a.snd ∈ B)).card^2 ≤ B.card * E[A] := by
  let r : G → ℕ := fun g => ((A ×ˢ A).filter (fun (a : G × G) => a.fst + a.snd = g)).card
  let T : Finset G := (A ×ˢ A).image (fun a => a.fst + a.snd)
  -- This should be a bit easier with a little extra API for additive energy
  have counting : E[A] = T.sum (fun b => (r b)^2)
  · let S := ((A ×ˢ A) ×ˢ A ×ˢ A).filter (fun (x : (G × G) × G × G) => x.1.1 + x.2.1 = x.1.2 + x.2.2)
    have temp : ∀ x : (G × G) × G × G, x ∈ S → x.1.2 + x.2.2 ∈ T
    · intro x hx
      rw [Finset.mem_image]
      use (x.1.2, x.2.2)
      refine ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp (Finset.mem_product.mp
        (Finset.mem_filter.mp hx).left).left).right, (Finset.mem_product.mp
        (Finset.mem_product.mp (Finset.mem_filter.mp hx).left).right).right⟩, rfl⟩
    rw [(show E[A] = S.card from rfl), Finset.card_eq_sum_card_fiberwise temp]
    suffices card_fiber : ∀ (g : G), g ∈ T →
      (S.filter (fun (x : (G × G) × G × G) => x.1.2 + x.2.2 = g)).card = (r g)^2
    · rw [Finset.sum_congr rfl card_fiber]
    suffices : ∀ (g : G), g ∈ T → S.filter (fun (x : (G × G) × G × G) => x.1.2 + x.2.2 = g)
      = (((A ×ˢ A).filter (fun x => x.1 + x.2 = g)) ×ˢ ((A ×ˢ A).filter (fun x => x.1 + x.2 = g))).image
      (fun x => ((x.1.1, x.2.1), x.1.2, x.2.2))
    · intro g hg
      rw [this g hg]
      simp only [Finset.mem_product, and_imp, Prod.forall, Finset.card_product,
        Finset.filter_congr_decidable, pow_two]
      rw [Finset.card_image_of_injective]
      · simp only [Finset.mem_product, and_imp, Prod.forall, Finset.card_product]
      · intro x y h
        simp only [Prod.mk.injEq] at h
        rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
        refine ⟨⟨h.left.left, h.right.left⟩, h.left.right, h.right.right⟩
    intro g _
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [Finset.mem_image]
      use ((x.1.1, x.2.1), x.1.2, x.2.2)
      refine ⟨?_, rfl⟩
      rw [Finset.mem_product]
      rw [Finset.mem_filter] at hx ⊢
      constructor
      · simp only [Finset.mem_product]
        constructor
        · exact ⟨(Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx.left).left).left).left,
          (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx.left).left).right).left⟩
        · rw [(Finset.mem_filter.mp hx.left).right, hx.right]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp
          (Finset.mem_product.mp (Finset.mem_filter.mp hx.left).left).left).right,
          (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hx.left).left).right).right⟩, hx.right⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ha.right.right⟩
      · simpa only [Finset.mem_product, Finset.mem_product, Finset.mem_product] using
          ⟨⟨ha.left.left.left, ha.right.left.left⟩, ha.left.left.right, ha.right.left.right⟩
      · rw [ha.left.right, ha.right.right]
  have rhs : ((A ×ˢ A).filter (fun (a : G × G) => a.fst + a.snd ∈ B)).card = B.sum r
  · rw [Finset.card_eq_sum_card_fiberwise (fun x hx => (Finset.mem_filter.mp hx).right)]
    apply Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.filter_filter]
    apply congr_arg _  (Finset.filter_congr (fun u _ => ⟨fun hu' => hu'.2, fun hu' => ⟨by rwa [hu'], hu'⟩⟩))
  suffices cauchy_schwarz : (B.sum r)^2 ≤ B.card * B.sum (fun b => (r b)^2)
  · rw [rhs]
    apply le_trans cauchy_schwarz _
    calc B.card * B.sum (fun b => (r b)^2) = B.card * (T ∩ B).sum (fun b => (r b)^2) := by
              suffices : B.sum (fun b => (r b)^2) = (T ∩ B).sum (fun b => (r b)^2)
              · rw [this]
              symm
              rw [Finset.sum_subset ((Finset.inter_subset_right T B))]
              intro x hx hx'
              rw [pow_two]
              have not_in : x ∉ T := fun hx'' => hx' (Finset.mem_inter_of_mem hx'' hx)
              have : ∀ y : G, y ∉ T → r y = 0
              · intro y hy
                rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
                intro t ht
                simp_rw [Finset.mem_filter] at ht hy
                simp_rw [Finset.mem_image] at hy
                apply hy ; use t
              rw [this x not_in, mul_zero]
        _ ≤ B.card * T.sum (fun b => (r b)^2) := by
              apply Nat.mul_le_mul_left
              rw [← Finset.sum_sdiff (Finset.inter_subset_left T B)]
              apply Nat.le_add_left _ _
        _ = B.card * E[A] := by rw [counting]
  have := nat_cauchy_schwartz' B r (fun _ => 1)
  have simp₁ : B.sum ((fun b => 1)^2) = B.card
  · simp only [Pi.pow_apply, one_pow, Finset.sum_const, smul_eq_mul, mul_one]
  have simp₂ : B.sum (r * fun g => 1) = B.sum r
  · simp only [Finset.mem_product, and_imp, Prod.forall, Pi.mul_apply, mul_one]
  rwa [simp₁, simp₂, mul_comm] at this


-- These are provisional values of constants, subject to change.  May also want to localize these definitions to just this file

def C₁ := 2^4
def C₂ := 1
def C₃ := 2^10
def C₄ := 4

/-- Let $G$ be an abelian group, and let $A$ be a finite non-empty set with $E(A) \geq |A|^3 / K$ for some $K \geq 1$.  Then there is a subset $A'$ of $A$ with $|A'| \geq |A| / (C_1 K^{C_2})$ and $|A'-A'| \leq C_3 K^{C_4} |A'|$ -/
lemma bsg (A : Finset G) (K : ℝ) (hK: 0 < K) (hE: E[A] ≥ (A.card)^3 / K): ∃ A' : Finset G, A' ⊆ A ∧ A'.card ≥ A.card / (C₁ * K^C₂) ∧ (A' - A').card ≤ C₃ * K^C₄ * A'.card := sorry

open scoped BigOperators
variable {G G' : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G']
  [ElementaryAddCommGroup G 2] [ElementaryAddCommGroup G' 2]

lemma equiv_filter_graph (f : G → G') :
    let A := (Set.graph f).toFinite.toFinset
    (A ×ˢ A).filter (fun (a, a') ↦ a + a' ∈ A) ≃
    { x : G × G | f (x.1 + x.2) = (f x.1) + (f x.2) } where
  toFun := fun ⟨a, ha⟩ ↦ by
    let A := (Set.graph f).toFinite.toFinset
    use (a.1.1, a.2.1)
    apply Finset.mem_filter.mp at ha
    have h {a} (h' : a ∈ A) := (Set.mem_graph _).mp <| (Set.graph f).toFinite.mem_toFinset.mp h'
    show f (a.1.1 + a.2.1) = (f a.1.1) + (f a.2.1)
    rw [h (Finset.mem_product.mp ha.1).1, h (Finset.mem_product.mp ha.1).2]
    exact h ha.2
  invFun := fun ⟨a, ha⟩ ↦ by
    use ((a.1, f a.1), (a.2, f a.2))
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    <;> apply (Set.graph f).toFinite.mem_toFinset.mpr
    · exact ⟨a.1, rfl⟩
    · exact ⟨a.2, rfl⟩
    · exact (Set.mem_graph _).mpr ha
  left_inv := fun ⟨x, hx⟩ ↦ by
    apply Subtype.ext
    show ((x.1.1, f x.1.1), x.2.1, f x.2.1) = x
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    rewrite [(Set.graph f).toFinite.mem_toFinset] at hx1 hx2
    rw [(Set.mem_graph x.1).mp hx1, (Set.mem_graph x.2).mp hx2]
  right_inv := fun _ ↦ rfl

set_option maxHeartbeats 400000 in
/-- Let $G, G'$ be finite abelian $2$-groups.
Let $f: G \to G'$ be a function, and suppose that there are at least
$|G|^2 / K$ pairs $(x,y) \in G^2$ such that $$ f(x+y) = f(x) + f(y).$$
Then there exists a homomorphism $\phi: G \to G'$ and a constant $c \in G'$ such that
$f(x) = \phi(x)+c$ for at least $|G| / C_1 C_3^{12} K^{24C_4 + 2C_2}$ values of $x \in G$. -/
theorem approx_hom_pfr (f : G → G') (K : ℝ) (hK: K > 0)
    (hf: Nat.card { x : G × G | f (x.1+x.2) = (f x.1) + (f x.2) } ≥ (Nat.card G)^2 / K) :
    ∃ (φ : G →+ G') (c : G'), Nat.card { x : G | f x = φ x + c } ≥
    (Nat.card G) / (C₁ * C₃^12 * K^(24 * C₄ + 2 * C₂)) := by
  let A := (Set.graph f).toFinite.toFinset

  have h_cs : ((A ×ˢ A).filter (fun (a, a') ↦ a + a' ∈ A) |>.card : ℝ) ^ 2 ≤
      Finset.card A * E[A] := by norm_cast; convert cauchy_schwarz A A
  rewrite [← Nat.card_eq_finsetCard, ← Nat.card_eq_finsetCard,
    Nat.card_congr (equiv_filter_graph f)] at h_cs

  have hA : Nat.card A = Nat.card G := by
    rewrite [← Set.card_graph f, Nat.card_eq_finsetCard, Set.Finite.card_toFinset]; simp
  have hA_pos : 0 < (Nat.card A : ℝ) := Nat.cast_pos.mpr <| Nat.card_pos.trans_eq hA.symm
  have : ((Nat.card G)^2 / K)^2 ≤ Nat.card A * E[A] := LE.le.trans (by gcongr) h_cs
  rewrite [← hA] at this
  replace : E[A] ≥ (Finset.card A)^3 / K^2 := calc
    _ ≥ ((Nat.card A)^2 / K)^2 / Nat.card A := (div_le_iff' <| hA_pos).mpr this
    _ = ((Nat.card A)^4 / (Nat.card A)) / K^2 := by ring
    _ = (Finset.card A)^3 / K^2 := by
      rw [pow_succ, mul_comm, mul_div_assoc, div_self (ne_of_gt hA_pos), mul_one,
        Nat.card_eq_finsetCard]
  obtain ⟨A', hA', hA'1, hA'2⟩ := bsg A (K^2) (sq_pos_of_pos hK) (by convert this)
  clear h_cs hf this

  let A'' := A'.toSet
  have hA''_coe : Nat.card A'' = Finset.card A' := Nat.card_eq_finsetCard A'
  have h_pos1 : 0 < (C₁ : ℝ) * (K ^ 2) ^ C₂ :=
    mul_pos (by unfold C₁; norm_num) (pow_pos (pow_pos hK 2) C₂)
  have hA''_pos : 0 < Nat.card A'' := by
    rewrite [hA''_coe, ← Nat.cast_pos (α := ℝ)]
    exact LT.lt.trans_le (div_pos (by rwa [← Nat.card_eq_finsetCard]) h_pos1) hA'1
  have hA''_nonempty : Set.Nonempty A'' := nonempty_subtype.mp (Finite.card_pos_iff.mp hA''_pos)
  have : Finset.card (A' - A') = Nat.card (A'' + A'') := calc
    _ = Nat.card (A' - A').toSet := (Nat.card_eq_finsetCard _).symm
    _ = Nat.card (A'' + A'') := by rw [Finset.coe_sub, sumset_eq_sub]
  replace :  Nat.card (A'' + A'') ≤ C₃ * (K ^ 2) ^ C₄ * (Nat.card A'') := by
    rewrite [← this, hA''_coe]
    convert hA'2
  obtain ⟨H, c, hc_card, hH_le, hH_ge, hH_cover⟩ := PFR_conjecture_improv_aux hA''_nonempty this
  clear hA'2 hA''_coe hH_le hH_ge hA_pos
  obtain ⟨H₀, H₁, φ, hH₀H₁, hH₀H₁_card⟩ := goursat H

  have h_le_H₀ : Nat.card A'' ≤ Nat.card c * Nat.card H₀ := by
    have h_le := Nat.card_mono (Set.toFinite _) (Set.image_subset Prod.fst hH_cover)
    have h_proj_A'' : Nat.card A'' = Nat.card (Prod.fst '' A'') := Nat.card_congr
      (Equiv.Set.imageOfInjOn Prod.fst A'' <|
        Set.InjOn.mono (Set.Finite.subset_toFinset.mp hA') (Set.fst_injOn_graph f))
    have h_proj_c : Prod.fst '' (c + H : Set (G × G')) = (Prod.fst '' c) + H₀ := by
      ext x ; constructor <;> intro hx
      · obtain ⟨x, ⟨⟨c, h, hc, hh, hch⟩, hx⟩⟩ := hx
        rewrite [← hx]
        use c.1, h.1
        exact ⟨Set.mem_image_of_mem Prod.fst hc, ((hH₀H₁ h).mp hh).1, (Prod.ext_iff.mp hch).1⟩
      · obtain ⟨_, h, ⟨c, hc⟩, hh, hch⟩ := hx
        refine ⟨c + Prod.mk h (φ h), ⟨⟨c, Prod.mk h (φ h), ?_⟩,  by rwa [← hc.2] at hch⟩⟩
        exact ⟨hc.1, (hH₀H₁ ⟨h, φ h⟩).mpr ⟨hh, by rw [sub_self]; apply zero_mem⟩, rfl⟩
    rewrite [← h_proj_A'', h_proj_c] at h_le
    apply (h_le.trans Set.card_add_le).trans
    gcongr
    exact Nat.card_image_le c.toFinite

  have hH₀_pos : (0 : ℝ) < Nat.card H₀ := Nat.cast_pos.mpr Nat.card_pos
  have h_le_H₁ : (Nat.card H₁ : ℝ) ≤ (Nat.card c) * (Nat.card H) / Nat.card A'' := calc
    _ = (Nat.card H : ℝ) / (Nat.card H₀) :=
      (eq_div_iff <| ne_of_gt <| hH₀_pos).mpr <| by rw [mul_comm, ← Nat.cast_mul, hH₀H₁_card]
    _ ≤ (Nat.card c : ℝ) * (Nat.card H) / Nat.card A'' := by
      nth_rewrite 1 [← mul_one (Nat.card H : ℝ), mul_comm (Nat.card c : ℝ)]
      repeat rewrite [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine le_of_mul_le_mul_right ?_ hH₀_pos
      refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.mpr hA''_pos)
      rewrite [div_mul_cancel 1, mul_right_comm, one_mul,  div_mul_cancel, ← Nat.cast_mul]
      · exact Nat.cast_le.mpr h_le_H₀
      · exact ne_of_gt (Nat.cast_pos.mpr hA''_pos)
      · exact ne_of_gt hH₀_pos
  clear h_le_H₀ hA''_pos hH₀_pos hH₀H₁_card

  let translate (c : G × G') (h : G') := A'' ∩ ({c} + {(0, h)} + Set.graph φ.toFun)
  have h_translate (c : G × G') (h : G') :
      Prod.fst '' translate c h ⊆ { x : G | f x = φ x + (-φ c.1 + c.2 + h) } := by
    intro x hx
    obtain ⟨x, ⟨⟨hxA'', ⟨_, x', ⟨c', h', hc, hh, hch⟩, hx, hchx⟩⟩, hxx⟩⟩ := hx
    show f _ = φ _ + (-φ c.1 + c.2 + h)
    replace := (Set.mem_graph x).mp <| (Set.graph f).toFinite.mem_toFinset.mp (hA' hxA'')
    rewrite [← hxx, this, ← hchx, ← hch, hc, hh]
    show c.2 + h + x'.2 = φ (c.1 + 0 + x'.1) + (-φ c.1 + c.2 + h)
    replace : φ x'.1 = x'.2 := (Set.mem_graph x').mp hx
    rw [map_add, map_add, map_zero, add_zero, this, add_comm (φ c.1), add_assoc x'.2,
      ← add_assoc (φ c.1), ← add_assoc (φ c.1), add_neg_self, zero_add, add_comm]
  have h_translate_card c h : Nat.card (translate c h) = Nat.card (Prod.fst '' translate c h) :=
    Nat.card_congr (Equiv.Set.imageOfInjOn Prod.fst (translate c h) <|
      Set.InjOn.mono (fun _ hx ↦ Set.Finite.subset_toFinset.mp hA' hx.1) (Set.fst_injOn_graph f))

  let cH₁ := (c ×ˢ H₁).toFinite.toFinset
  haveI A_nonempty : Nonempty A'' := Set.nonempty_coe_sort.mpr hA''_nonempty
  replace : Nonempty c := by
    obtain ⟨c, _, hc, _, _⟩ := hH_cover (Classical.choice A_nonempty).property
    exact ⟨c, hc⟩
  replace h_nonempty : Set.Nonempty (c ×ˢ H₁) :=
    Set.Nonempty.prod (Set.nonempty_coe_sort.mp this) (Set.nonempty_coe_sort.mp inferInstance)
  replace : A' = Finset.biUnion cH₁ fun ch ↦ (translate ch.1 ch.2).toFinite.toFinset := by
    ext x ; constructor <;> intro hx
    · obtain ⟨c', h, hc, hh, hch⟩ := hH_cover hx
      refine Finset.mem_biUnion.mpr ⟨(c', h.2 - φ h.1), ?_⟩
      refine ⟨(Set.Finite.mem_toFinset _).mpr ⟨hc, ((hH₀H₁ h).mp hh).2⟩, ?_⟩
      refine (Set.Finite.mem_toFinset _).mpr ⟨hx, ⟨c' + (0, h.2 - φ h.1), (h.1, φ h.1), ?_⟩⟩
      refine ⟨⟨c', (0, h.2 - φ h.1), rfl, rfl, rfl⟩, ⟨⟨h.1, rfl⟩, ?_⟩⟩
      beta_reduce
      rewrite [add_assoc]
      show c' + (0 + h.1, h.2 - φ h.1 + φ h.1) = x
      rewrite [zero_add, sub_add_cancel]
      exact hch
    · obtain ⟨ch, hch⟩ := Finset.mem_biUnion.mp hx
      exact ((Set.Finite.mem_toFinset _).mp hch.2).1

  replace : ∑ __ in cH₁, ((Finset.card A) / (C₁ * (K ^ 2) ^ C₂) / cH₁.card : ℝ) ≤
      ∑ ch in cH₁, ((translate ch.1 ch.2).toFinite.toFinset.card : ℝ) := by
    rewrite [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_div_right_comm, div_self, one_mul]
    · apply hA'1.trans
      norm_cast
      exact (congrArg Finset.card this).trans_le Finset.card_biUnion_le
    · symm
      refine ne_of_lt <| Nat.cast_zero.symm.trans_lt <| Nat.cast_lt.mpr <| Finset.card_pos.mpr ?_
      exact (Set.Finite.toFinset_nonempty _).mpr h_nonempty
  replace : ∃ c' : G × G', ∃ h : G', (Finset.card A) / (C₁ * (K ^ 2) ^ C₂) / cH₁.card ≤
      Nat.card { x : G | f x = φ x + (-φ c'.1 + c'.2 + h) } := by
    obtain ⟨ch, hch⟩ :=
      Finset.exists_le_of_sum_le ((Set.Finite.toFinset_nonempty _).mpr h_nonempty) this
    refine ⟨ch.1, ch.2, hch.2.trans ?_⟩
    rewrite [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card, h_translate_card]
    exact Nat.cast_le.mpr <| Nat.card_mono (Set.toFinite _) (h_translate ch.1 ch.2)
  clear hA' hA'1 hH_cover hH₀H₁ translate h_translate h_translate_card

  obtain ⟨c', h, hch⟩ := this
  use φ, -φ c'.1 + c'.2 + h
  refine LE.le.trans ?_ hch
  unfold_let cH₁
  rewrite [← Nat.card_eq_finsetCard, div_div, hA]
  apply div_le_div_of_le_left (Nat.cast_nonneg _) <| mul_pos h_pos1 <| Nat.cast_pos.mpr <|
    Finset.card_pos.mpr <| (Set.Finite.toFinset_nonempty _).mpr h_nonempty
  rewrite [← c.toFinite.toFinset_prod (H₁ : Set G').toFinite, Finset.card_product]
  repeat rewrite [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]
  rewrite [Nat.cast_mul, ← mul_assoc _ (Nat.card c : ℝ)]
  replace := mul_nonneg h_pos1.le (Nat.cast_nonneg (Nat.card c))
  apply (mul_le_mul_of_nonneg_left h_le_H₁ this).trans
  rewrite [mul_div_assoc, ← mul_assoc, mul_comm _ (Nat.card c : ℝ), mul_assoc]
  have hHA := div_nonneg (α := ℝ) (Nat.cast_nonneg (Nat.card H)) <| Nat.cast_nonneg (Nat.card A'')
  apply (mul_le_mul_of_nonneg_right hc_card <| mul_nonneg this hHA).trans
  rewrite [mul_comm, mul_assoc, mul_comm _ (Nat.card c : ℝ), mul_assoc]
  refine (mul_le_mul_of_nonneg_right hc_card ?_).trans_eq ?_
  · exact mul_nonneg h_pos1.le <| mul_nonneg hHA <| by positivity
  have h_pos2 : 0 < (C₃ : ℝ) * (K ^ 2) ^ C₄ :=
    mul_pos (by unfold C₃; norm_num) (pow_pos (pow_pos hK 2) C₄)
  rewrite [mul_comm, mul_assoc, mul_assoc, mul_assoc, mul_mul_mul_comm,
    ← Real.rpow_add (Nat.cast_pos.mpr Nat.card_pos), mul_mul_mul_comm,
    ← Real.rpow_add (Nat.cast_pos.mpr Nat.card_pos), ← Real.rpow_add h_pos2]
  norm_num
  rewrite [mul_comm _ (Finset.card A' : ℝ), mul_assoc (Finset.card A' : ℝ),
    ← mul_assoc _ (Finset.card A' : ℝ), div_mul_cancel _ <|
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hA''_nonempty).ne.symm, Real.rpow_neg_one,
    mul_comm (Fintype.card H : ℝ), mul_assoc _ _ (Fintype.card H : ℝ),
    inv_mul_cancel <| NeZero.natCast_ne _ _, mul_one, ← pow_mul,
    Real.mul_rpow (by norm_num) (pow_nonneg (sq_nonneg K) C₄), ← pow_mul,
    mul_comm (K ^ _), mul_assoc _ _ (K ^ _)]
  repeat rewrite [show (12 : ℝ) = ((12 : ℕ) : ℝ) from rfl]
  repeat rewrite [Real.rpow_nat_cast]
  rewrite [← pow_mul, ← pow_add, mul_right_comm, ← mul_assoc]
  norm_num
