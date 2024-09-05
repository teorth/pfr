import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import LeanAPAP.Extras.BSG
import PFR.HomPFR

/-!
# The approximate homomorphism form of PFR

Here we apply PFR to show that almost homomorphisms f from a 2-group to a 2-group often coincide
with a (shifted) actual homomorphisms.  Here, approximate is in the sense that f(x+y)=f(x)+f(y)
is true for a positive proportion of x,y.

## Main result

* `approx_hom_pfr` : If $f: G → G'$ is a map between finite abelian elementary 2-groups such that
  $f(x+y)=f(x)+f(y)$ for at least $|G|/K$ values, then then there is a homomorphism $\phi: G \to G'$
  and a constant $c$ such that $f(x)=\phi(x)+c$ for a substantial set of values.
-/

open Finset
open scoped Classical Pointwise Combinatorics.Additive

variable {G G' : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G']
  [ElementaryAddCommGroup G 2] [ElementaryAddCommGroup G' 2] (A : Finset G)

/-- Let $G, G'$ be finite abelian $2$-groups.
Let $f : G \to G'$ be a function, and suppose that there are at least
$|G|^2 / K$ pairs $(x,y) \in G^2$ such that $$ f(x+y) = f(x) + f(y).$$
Then there exists a homomorphism $\phi : G \to G'$ and a constant $c \in G'$ such that
$f(x) = \phi(x)+c$ for at least $|G| / (2 ^ {172} * K ^ {146})$ values of $x \in G$. -/
theorem approx_hom_pfr (f : G → G') (K : ℝ) (hK : K > 0)
    (hf : Nat.card {x : G × G | f (x.1 + x.2) = f x.1 + f x.2} ≥ Nat.card G ^ 2 / K) :
    ∃ (φ : G →+ G') (c : G'), Nat.card {x | f x = φ x + c} ≥ Nat.card G / (2 ^ 172 * K ^ 146) := by
  let A := (Set.graph f).toFinite.toFinset

  have h_cs : ((A ×ˢ A).filter (fun (a, a') ↦ a + a' ∈ A) |>.card : ℝ) ^ 2 ≤
      Finset.card A * E[A] := by
    norm_cast
    convert card_sq_le_card_mul_addEnergy A A A
  rewrite [← Nat.card_eq_finsetCard, ← Nat.card_eq_finsetCard,
    Nat.card_congr (Set.equivFilterGraph f)] at h_cs

  have hA : Nat.card A = Nat.card G := by
    rewrite [← Set.card_graph f, Nat.card_eq_finsetCard, Set.Finite.card_toFinset]; simp
  have hA_pos : 0 < (Nat.card A : ℝ) := Nat.cast_pos.mpr <| Nat.card_pos.trans_eq hA.symm
  have : ((Nat.card G)^2 / K)^2 ≤ Nat.card A * E[A] := LE.le.trans (by gcongr) h_cs
  rewrite [← hA] at this
  replace : E[A] ≥ (Finset.card A)^3 / K^2 := calc
    _ ≥ ((Nat.card A)^2 / K)^2 / Nat.card A := (div_le_iff₀' <| hA_pos).mpr this
    _ = ((Nat.card A)^4 / (Nat.card A)) / K^2 := by ring
    _ = (Finset.card A)^3 / K^2 := by
      rw [pow_succ, mul_div_assoc, div_self (ne_of_gt hA_pos), mul_one,
        Nat.card_eq_finsetCard]
  have hA_nonempty : A.Nonempty := (Set.Finite.toFinset_nonempty _).2 $ Set.graph_nonempty _
  obtain ⟨A', hA', hA'1, hA'2⟩ :=
    BSG_self' (sq_nonneg K) hA_nonempty (by simpa only [inv_mul_eq_div] using this)
  clear h_cs hf this
  have hA'₀ : A'.Nonempty := Finset.card_pos.1 $ Nat.cast_pos.1 $ hA'1.trans_lt' $ by positivity
  let A'' := A'.toSet
  have hA''_coe : Nat.card A'' = Finset.card A' := Nat.card_eq_finsetCard A'
  have hA''_pos : 0 < Nat.card A'' := by rw [hA''_coe]; exact hA'₀.card_pos
  have hA''_nonempty : Set.Nonempty A'' := nonempty_subtype.mp (Finite.card_pos_iff.mp hA''_pos)
  have : Finset.card (A' - A') = Nat.card (A'' + A'') := calc
    _ = Nat.card (A' - A').toSet := (Nat.card_eq_finsetCard _).symm
    _ = Nat.card (A'' + A'') := by rw [Finset.coe_sub, sumset_eq_sub]
  replace : Nat.card (A'' + A'') ≤ 2 ^ 14 * K ^ 12 * Nat.card A'' := by
    rewrite [← this, hA''_coe]
    simpa [← pow_mul] using hA'2
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
      · obtain ⟨x, ⟨⟨c, hc, h, hh, hch⟩, hx⟩⟩ := hx
        rewrite [← hx]
        exact ⟨c.1, Set.mem_image_of_mem Prod.fst hc, h.1, ((hH₀H₁ h).mp hh).1, (Prod.ext_iff.mp hch).1⟩
      · obtain ⟨_, ⟨c, hc⟩, h, hh, hch⟩ := hx
        refine ⟨c + (h, φ h), ⟨⟨c, hc.1, (h, φ h), ?_⟩, by rwa [← hc.2] at hch⟩⟩
        exact ⟨(hH₀H₁ ⟨h, φ h⟩).mpr ⟨hh, by rw [sub_self]; apply zero_mem⟩, rfl⟩
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
      rewrite [div_mul_cancel₀ 1, mul_right_comm, one_mul, div_mul_cancel₀, ← Nat.cast_mul]
      · exact Nat.cast_le.mpr h_le_H₀
      · exact ne_of_gt (Nat.cast_pos.mpr hA''_pos)
      · exact ne_of_gt hH₀_pos
  clear h_le_H₀ hA''_pos hH₀_pos hH₀H₁_card

  let translate (c : G × G') (h : G') := A'' ∩ ({c} + {(0, h)} + Set.graph φ.toFun)
  have h_translate (c : G × G') (h : G') :
      Prod.fst '' translate c h ⊆ { x : G | f x = φ x + (-φ c.1 + c.2 + h) } := by
    intro x hx
    obtain ⟨x, ⟨⟨hxA'', ⟨_, ⟨c', hc, h', hh, hch⟩, x', hx, hchx⟩⟩, hxx⟩⟩ := hx
    show f _ = φ _ + (-φ c.1 + c.2 + h)
    replace := (Set.mem_graph x).mp <| (Set.graph f).toFinite.mem_toFinset.mp (hA' hxA'')
    rewrite [← hxx, this, ← hchx, ← hch, hc, hh]
    show c.2 + h + x'.2 = φ (c.1 + 0 + x'.1) + (-φ c.1 + c.2 + h)
    replace : φ x'.1 = x'.2 := (Set.mem_graph x').mp hx
    rw [map_add, map_add, map_zero, add_zero, this, add_comm (φ c.1), add_assoc x'.2,
      ← add_assoc (φ c.1), ← add_assoc (φ c.1), ← sub_eq_add_neg, sub_self, zero_add, add_comm]
  have h_translate_card c h : Nat.card (translate c h) = Nat.card (Prod.fst '' translate c h) :=
    Nat.card_congr (Equiv.Set.imageOfInjOn Prod.fst (translate c h) <|
      Set.InjOn.mono (fun _ hx ↦ Set.Finite.subset_toFinset.mp hA' hx.1) (Set.fst_injOn_graph f))

  let cH₁ := (c ×ˢ H₁).toFinite.toFinset
  haveI A_nonempty : Nonempty A'' := Set.nonempty_coe_sort.mpr hA''_nonempty
  replace : Nonempty c := by
    obtain ⟨c, hc, _, _, _⟩ := hH_cover (Classical.choice A_nonempty).property
    exact ⟨c, hc⟩
  replace h_nonempty : Set.Nonempty (c ×ˢ H₁) :=
    Set.Nonempty.prod (Set.nonempty_coe_sort.mp this) (Set.nonempty_coe_sort.mp inferInstance)
  replace : A' = Finset.biUnion cH₁ fun ch ↦ (translate ch.1 ch.2).toFinite.toFinset := by
    ext x ; constructor <;> intro hx
    · obtain ⟨c', hc, h, hh, hch⟩ := hH_cover hx
      refine Finset.mem_biUnion.mpr ⟨(c', h.2 - φ h.1), ?_⟩
      refine ⟨(Set.Finite.mem_toFinset _).mpr ⟨hc, ((hH₀H₁ h).mp hh).2⟩, ?_⟩
      refine (Set.Finite.mem_toFinset _).mpr ⟨hx, c' + (0, h.2 - φ h.1), ?_⟩
      refine ⟨⟨c', rfl, (0, h.2 - φ h.1), rfl, rfl⟩, (h.1, φ h.1), ⟨h.1, rfl⟩, ?_⟩
      beta_reduce
      rewrite [add_assoc]
      show c' + (0 + h.1, h.2 - φ h.1 + φ h.1) = x
      rewrite [zero_add, sub_add_cancel]
      exact hch
    · obtain ⟨ch, hch⟩ := Finset.mem_biUnion.mp hx
      exact ((Set.Finite.mem_toFinset _).mp hch.2).1

  replace : ∑ __ in cH₁, ((2 ^ 4)⁻¹ * (K ^ 2)⁻¹ * A.card / cH₁.card : ℝ) ≤
      ∑ ch in cH₁, ((translate ch.1 ch.2).toFinite.toFinset.card : ℝ) := by
    rewrite [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_div_right_comm, div_self, one_mul]
    · apply hA'1.trans
      norm_cast
      exact (congrArg Finset.card this).trans_le Finset.card_biUnion_le
    · symm
      refine ne_of_lt <| Nat.cast_zero.symm.trans_lt <| Nat.cast_lt.mpr <| Finset.card_pos.mpr ?_
      exact (Set.Finite.toFinset_nonempty _).mpr h_nonempty
  replace : ∃ c' : G × G', ∃ h : G', (2 ^ 4 : ℝ)⁻¹ * (K ^ 2)⁻¹ * A.card / cH₁.card ≤
      Nat.card { x : G | f x = φ x + (-φ c'.1 + c'.2 + h) } := by
    obtain ⟨ch, hch⟩ :=
      Finset.exists_le_of_sum_le ((Set.Finite.toFinset_nonempty _).mpr h_nonempty) this
    refine ⟨ch.1, ch.2, hch.2.trans ?_⟩
    rewrite [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card, h_translate_card]
    exact Nat.cast_le.mpr <| Nat.card_mono (Set.toFinite _) (h_translate ch.1 ch.2)
  clear hA' hA'1 hH_cover hH₀H₁ translate h_translate h_translate_card

  obtain ⟨c', h, hch⟩ := this
  use φ, -φ c'.1 + c'.2 + h
  refine le_trans ?_ hch
  unfold_let cH₁
  rewrite [← Nat.card_eq_finsetCard, hA, ← mul_inv, inv_mul_eq_div, div_div]
  apply div_le_div (Nat.cast_nonneg _) le_rfl
  · apply mul_pos
    · apply mul_pos
      · norm_num
      · exact sq_pos_of_pos hK
    · rewrite [Nat.cast_pos, Finset.card_pos, Set.Finite.toFinset_nonempty _]
      exact h_nonempty
  rw [show 146 = 2 + 144 by norm_num, show 172 = 4 + 168 by norm_num, pow_add, pow_add,
    mul_mul_mul_comm]
  gcongr
  rewrite [← c.toFinite.toFinset_prod (H₁ : Set G').toFinite, Finset.card_product]
  repeat rewrite [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]
  push_cast
  refine (mul_le_mul_of_nonneg_left h_le_H₁ (Nat.cast_nonneg _)).trans ?_
  refine (mul_le_mul_of_nonneg_right hc_card (by positivity)).trans ?_
  rewrite [mul_div_left_comm, mul_assoc]
  refine (mul_le_mul_of_nonneg_right hc_card (by positivity)).trans_eq ?_
  rw [mul_assoc ((_ * _)^6), mul_mul_mul_comm, mul_comm (_ ^ (1/2) * _), mul_comm_div,
    ← mul_assoc _ (_^_) (_^_), mul_div_assoc, mul_mul_mul_comm _ (_^_) (_^_),
    ← mul_div_assoc, mul_assoc _ (_^(1/2)) (_^(1/2)),
    ← Real.rpow_add (Nat.cast_pos.mpr Nat.card_pos), add_halves, Real.rpow_one,
    ← Real.rpow_add (Nat.cast_pos.mpr Nat.card_pos), add_halves, Real.rpow_neg_one,
    mul_comm _ (_ / _), mul_assoc (_^6)]
  conv => { lhs; rhs; rw [← mul_assoc, ← mul_div_assoc, mul_comm_div, mul_div_assoc] }
  rw [div_self <| Nat.cast_ne_zero.mpr (Nat.ne_of_lt Nat.card_pos).symm, mul_one]
  push_cast
  rw [mul_inv_cancel₀ <| Nat.cast_ne_zero.mpr (Nat.ne_of_lt Nat.card_pos).symm, one_mul, ← sq,
    ← Real.rpow_two, ← Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  have : K ^ (12 : ℕ) = K ^ (12 : ℝ) := (Real.rpow_natCast K 12).symm
  rw [this, ← Real.rpow_mul (by positivity)]
  norm_num
  exact Real.rpow_natCast K 144
