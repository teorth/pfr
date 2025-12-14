import Mathlib.Data.FunLike.Fintype
import Mathlib.Data.Int.Lemmas

import LeanAPAP.Extras.BSG

import PFR.HomPFR

/-!
# The approximate homomorphism form of PFR

Here we apply PFR to show that almost homomorphisms f from a 2-group to a 2-group often coincide
with a (shifted) actual homomorphisms. Here, approximate is in the sense that f(x+y)=f(x)+f(y)
is true for a positive proportion of x,y.

## Main result

* `approx_hom_pfr` : If $f: G → G'$ is a map between finite abelian elementary 2-groups such that
  $f(x+y)=f(x)+f(y)$ for at least $|G|/K$ values, then then there is a homomorphism $\phi: G \to G'$
  and a constant $c$ such that $f(x)=\phi(x)+c$ for a substantial set of values.
-/

open Finset Module
open scoped Pointwise Combinatorics.Additive

variable {G G' : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup G'] [Fintype G']
  [Module (ZMod 2) G] [Module (ZMod 2) G'] (A : Finset G)

/-- Let $G, G'$ be finite abelian $2$-groups.
Let $f : G \to G'$ be a function, and suppose that there are at least
$|G|^2 / K$ pairs $(x,y) \in G^2$ such that $$ f(x+y) = f(x) + f(y).$$
Then there exists a homomorphism $\phi : G \to G'$ and a constant $c \in G'$ such that
$f(x) = \phi(x)+c$ for at least $|G| / (2 ^ {144} * K ^ {122})$ values of $x \in G$. -/
theorem approx_hom_pfr (f : G → G') (K : ℝ) (hK : K > 0)
    (hf : Nat.card G ^ 2 / K ≤ Nat.card {x : G × G | f (x.1 + x.2) = f x.1 + f x.2}) :
    ∃ (φ : G →+ G') (c : G'), Nat.card {x | f x = φ x + c} ≥ Nat.card G / (2 ^ 144 * K ^ 122) := by
  classical
  let A := (Set.univ.graphOn f).toFinite.toFinset
  have hA : #A = Nat.card G := by rw [Set.Finite.card_toFinset]; simp [← Nat.card_eq_fintype_card]
  have hA_nonempty : A.Nonempty := by simp [-Set.Finite.toFinset_setOf, A]
  have := calc
    (#A ^ 3 / K ^ 2 : ℝ)
      = (Nat.card G ^ 2 / K) ^ 2 / #A := by simp [hA]; field_simp
    _ ≤ Nat.card {x : G × G | f (x.1 + x.2) = f x.1 + f x.2} ^ 2 / #A := by gcongr
    _ = #{ab ∈ A ×ˢ A | ab.1 + ab.2 ∈ A} ^ 2 / #A := by
      congr
      rw [← Nat.card_eq_finsetCard, ← Finset.coe_sort_coe, Finset.coe_filter,
        Set.Finite.toFinset_prod]
      simp only [Set.Finite.mem_toFinset, A, Set.graphOn_prod_graphOn]
      rw [← Set.natCard_graphOn _ (Prod.map f f),
        ← Nat.card_image_equiv (Equiv.prodProdProdComm G G' G G'), Equiv.image_eq_preimage_symm]
      congr
      aesop
    _ ≤ #A * E[A] / #A := by gcongr; exact mod_cast card_sq_le_card_mul_addEnergy ..
    _ = E[A] := by field_simp
  obtain ⟨A', hA', hA'1, hA'2⟩ :=
    BSG_self' (sq_nonneg K) hA_nonempty (by simpa only [inv_mul_eq_div] using this)
  clear hf this
  have hA'₀ : A'.Nonempty := Finset.card_pos.1 <| Nat.cast_pos.1 <| hA'1.trans_lt' <| by positivity
  let A'' : Set (G × G') := A'
  have hA''_coe : Nat.card A'' = #A' := Nat.card_eq_finsetCard A'
  have hA''_pos : 0 < Nat.card A'' := by rw [hA''_coe]; exact hA'₀.card_pos
  have hA''_nonempty : Set.Nonempty A'' := nonempty_subtype.mp (Finite.card_pos_iff.mp hA''_pos)
  have : (A' - A').card = (A'' + A'').ncard := by simp [A'', ← Finset.coe_sub, sumset_eq_sub]
  replace : (A'' + A'').ncard ≤ 2 ^ 14 * K ^ 12 * Nat.card A'' := by
    rewrite [← this, hA''_coe]
    simpa [← pow_mul] using hA'2
  obtain ⟨H, c, hc_card, hH_le, hH_ge, hH_cover⟩ := better_PFR_conjecture_aux hA''_nonempty this
  clear hA'2 hA''_coe hH_le hH_ge
  obtain ⟨H₀, H₁, φ, hH₀H₁, hH₀H₁_card⟩ := goursat H
  have h_le_H₀ : Nat.card A'' ≤ Nat.card c * Nat.card H₀ := by
    have h_le := Nat.card_mono (Set.toFinite _) (Set.image_mono (f := Prod.fst) hH_cover)
    have h_proj_A'' : Nat.card A'' = Nat.card (Prod.fst '' A'') := Nat.card_congr
      (Equiv.Set.imageOfInjOn Prod.fst A'' <|
        Set.fst_injOn_graph.mono (Set.Finite.subset_toFinset.mp hA'))
    have h_proj_c : Prod.fst '' (c + H : Set (G × G')) = (Prod.fst '' c) + H₀ := by
      ext x ; constructor <;> intro hx
      · obtain ⟨x, ⟨⟨c, hc, h, hh, hch⟩, hx⟩⟩ := hx
        rewrite [← hx]
        exact ⟨c.1, Set.mem_image_of_mem Prod.fst hc, h.1, ((hH₀H₁ h).mp hh).1,
          (Prod.ext_iff.mp hch).1⟩
      · obtain ⟨_, ⟨c, hc⟩, h, hh, hch⟩ := hx
        refine ⟨c + (h, φ h), ⟨⟨c, hc.1, (h, φ h), ?_⟩, by rwa [← hc.2] at hch⟩⟩
        exact ⟨(hH₀H₁ ⟨h, φ h⟩).mpr ⟨hh, by rw [sub_self]; apply zero_mem⟩, rfl⟩
    rewrite [← h_proj_A'', h_proj_c] at h_le
    apply (h_le.trans Set.natCard_add_le).trans
    gcongr
    · exact Finite.card_image_le Prod.fst
    · exact Nat.card_le_card_of_injective (fun ⦃a₁⦄ ↦ a₁) fun ⦃a₁ a₂⦄ a ↦ a
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
  let translate (c : G × G') (h : G') := A'' ∩ ({c} + {(0, h)} + Set.univ.graphOn φ)
  have h_translate (c : G × G') (h : G') :
      Prod.fst '' translate c h ⊆ { x : G | f x = φ x + (-φ c.1 + c.2 + h) } := by
    intro x hx
    obtain ⟨x, ⟨hxA'', _, ⟨c', hc, h', hh, hch⟩, x', hx, hchx⟩, hxx⟩ := hx
    change f _ = φ _ + (-φ c.1 + c.2 + h)
    replace := by simpa [-Set.Finite.toFinset_setOf, A] using hA' hxA''
    rewrite [← hxx, this, ← hchx, ← hch, hc, hh]
    change c.2 + h + x'.2 = φ (c.1 + 0 + x'.1) + (-φ c.1 + c.2 + h)
    replace : φ x'.1 = x'.2 := (Set.mem_graphOn.mp hx).2
    rw [map_add, map_add, map_zero, add_zero, this, add_comm (φ c.1), add_assoc x'.2,
      ← add_assoc (φ c.1), ← add_assoc (φ c.1), ← sub_eq_add_neg, sub_self, zero_add, add_comm]
  have h_translate_card c h : Nat.card (translate c h) = Nat.card (Prod.fst '' translate c h) :=
    Nat.card_congr (Equiv.Set.imageOfInjOn Prod.fst (translate c h) <|
      Set.fst_injOn_graph.mono fun _ hx ↦ Set.Finite.subset_toFinset.mp hA' hx.1)
  let cH₁ := (c ×ˢ H₁).toFinite.toFinset
  have A_nonempty : Nonempty A'' := Set.nonempty_coe_sort.mpr hA''_nonempty
  replace hc : c.Nonempty := by
    obtain ⟨x, hx, _, _, _⟩ := hH_cover (Classical.choice A_nonempty).property
    exact ⟨x, hx⟩
  replace : A' = Finset.biUnion cH₁ fun ch ↦ (translate ch.1 ch.2).toFinite.toFinset := by
    ext x ; constructor <;> intro hx
    · obtain ⟨c', hc, h, hh, hch⟩ := hH_cover hx
      refine Finset.mem_biUnion.mpr ⟨(c', h.2 - φ h.1), ?_⟩
      refine ⟨(Set.Finite.mem_toFinset _).mpr ⟨hc, ((hH₀H₁ h).mp hh).2⟩, ?_⟩
      refine (Set.Finite.mem_toFinset _).mpr ⟨hx, c' + (0, h.2 - φ h.1), ?_⟩
      refine ⟨⟨c', rfl, (0, h.2 - φ h.1), rfl, rfl⟩, (h.1, φ h.1), ⟨h.1, by simp⟩, ?_⟩
      beta_reduce
      rewrite [add_assoc]
      change c' + (0 + h.1, h.2 - φ h.1 + φ h.1) = x
      rewrite [zero_add, sub_add_cancel]
      exact hch
    · obtain ⟨ch, hch⟩ := Finset.mem_biUnion.mp hx
      exact ((Set.Finite.mem_toFinset _).mp hch.2).1
  replace : ∑ _ ∈ cH₁, ((2 ^ 4)⁻¹ * (K ^ 2)⁻¹ * #A / cH₁.card : ℝ) ≤
      ∑ ch ∈ cH₁, ((translate ch.1 ch.2).toFinite.toFinset.card : ℝ) := by
    rewrite [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_div_right_comm, div_self, one_mul]
    · apply hA'1.trans
      norm_cast
      exact (congrArg Finset.card this).trans_le Finset.card_biUnion_le
    · symm
      refine ne_of_lt <| Nat.cast_zero.symm.trans_lt <| Nat.cast_lt.mpr <| Finset.card_pos.mpr ?_
      exact (Set.Finite.toFinset_nonempty _).mpr <| hc.prod H₁.nonempty
  obtain ⟨c', h, hch⟩ : ∃ c' : G × G', ∃ h : G', (2 ^ 4 : ℝ)⁻¹ * (K ^ 2)⁻¹ * #A / cH₁.card ≤
      Nat.card { x : G | f x = φ x + (-φ c'.1 + c'.2 + h) } := by
    obtain ⟨ch, hch⟩ :=
      Finset.exists_le_of_sum_le ((Set.Finite.toFinset_nonempty _).mpr (hc.prod H₁.nonempty)) this
    refine ⟨ch.1, ch.2, hch.2.trans ?_⟩
    rewrite [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card, h_translate_card]
    exact Nat.cast_le.mpr <| Nat.card_mono (Set.toFinite _) (h_translate ch.1 ch.2)
  clear! hA' hA'1 hH_cover hH₀H₁ translate h_translate h_translate_card
  use φ, -φ c'.1 + c'.2 + h
  calc
    Nat.card G / (2 ^ 144 * K ^ 122)
    _ = Nat.card G / (2 ^ 4 * K ^ 2 * (2 ^ 140 * K ^ 120)) := by ring
    _ ≤ Nat.card G / (2 ^ 4 * K ^ 2 * #(c ×ˢ H₁).toFinite.toFinset) := ?_
    _ = (2 ^ 4)⁻¹ * (K ^ 2)⁻¹ * ↑(#A) / ↑(#cH₁) := by rw [hA, ← mul_inv, inv_mul_eq_div, div_div]
    _ ≤ _ := hch
  have := (c ×ˢ H₁).toFinite.toFinset_nonempty.2 (hc.prod H₁.nonempty)
  gcongr
  calc
    (#(c ×ˢ H₁).toFinite.toFinset : ℝ)
    _ = #c.toFinite.toFinset * #(H₁ : Set G').toFinite.toFinset := by
      rw [← Nat.cast_mul, ← Finset.card_product, Set.Finite.toFinset_prod]
    _ = Nat.card c * Nat.card H₁ := by
      simp_rw [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card]; norm_cast
    _ ≤ Nat.card c * (Nat.card c * Nat.card H / Nat.card ↑A'') := by gcongr
    _ = Nat.card c ^ 2 * Nat.card H / Nat.card ↑A'' := by ring
    _ ≤ ((2 ^ 14 * K ^ 12) ^ 5 * Nat.card A'' ^ (1 / 2 : ℝ) * Nat.card H ^ (-1 / 2 : ℝ)) ^ 2 *
          Nat.card H / Nat.card ↑A'' := by gcongr; exact hc_card
    _ = 2 ^ 140 * K ^ 120 := by simp; field_simp; rpow_simp; norm_num

/-- Non canonical isomorphism between a finite 2-torsion group and its dual into `ZMod 2`. -/
noncomputable def dual_iso : G ≃+ (G →+ ZMod 2) := by
  -- By definition of dual space, we know that $G^*$ is isomorphic to
  -- $\text{Hom}(G, \mathbb{Z}/2\mathbb{Z})$.
  have hdual_iso_hom : (G →+ ZMod 2) ≃+ Module.Dual (ZMod 2) G :=
    AddMonoidHom.toZModLinearMapEquiv 2;
  -- Since $G$ is a finite-dimensional vector space over $\mathbb{Z}/2\mathbb{Z}$, it is isomorphic
  -- to its dual space.
  have h_dual_iso_self : G ≃ₗ[ZMod 2] Module.Dual (ZMod 2) G :=
    (Basis.linearEquiv_dual_iff_finiteDimensional.mpr inferInstance).some
  exact h_dual_iso_self.toAddEquiv.trans hdual_iso_hom.symm

theorem card_of_dual : Nat.card (G →+ ZMod 2) = Nat.card G := Nat.card_congr dual_iso.toEquiv.symm

theorem card_of_dual_constrained (x : G) (hx : x ≠ 0) :
    2 * Nat.card { φ: G →+ ZMod 2 | φ x = 1 } = Nat.card G := by
  suffices h_eq_card :
      Nat.card {φ : G →+ ZMod 2 | φ x = 1} = Nat.card {φ : G →+ ZMod 2 | φ x = 0} by
    have h_eq_card :
        Nat.card {φ : G →+ ZMod 2 | φ x = 1} + Nat.card {φ : G →+ ZMod 2 | φ x = 0} =
          Nat.card (G →+ ZMod 2) := by
      -- These two sets partition the set of all homomorphisms from $G$ to $\mathbb{Z}/2\mathbb{Z}$.
      trans Nat.card (Set.univ : Set (G →+ ZMod 2))
      · -- Since these two sets partition the set of all homomorphisms from $G$ to
        -- $\mathbb{Z}/2\mathbb{Z}$, their cardinalities add up to the cardinality of the whole set.
        have h_partition : {φ : G →+ ZMod 2 | φ x = 1} ∪ {φ : G →+ ZMod 2 | φ x = 0} = .univ := by
          ext f
          cases Fin.exists_fin_two.mp ⟨f x, rfl⟩ <;> simp [*]
        have _ := DFunLike.finite (G →+ ZMod 2)
        rw [← h_partition, Nat.card_congr <| Equiv.Set.union <| Set.disjoint_left.mpr <| by
          simp +contextual]
        simp [Nat.card, Cardinal.toNat_add]
      · simp
    -- Since there are $|G|$ homomorphisms in total, we have $|G| = |H_1| + |H_0|$.
    simp_all only [ne_eq, Set.coe_setOf, card_of_dual, Nat.card_eq_fintype_card]
    rw [← h_eq_card]; ring
  -- Let $y$ be an additive character of $G$ such that $y(x) = 1$.
  obtain ⟨y, hy⟩ : ∃ (y : G →+ ZMod 2), y x = 1 := by
    -- Since $G$ is finite, there exists $y : G →+ ZMod 2$ such that
    -- $\forall z, y z = \sum_{z \in \{x\}} z$. Let's choose any such $y$.
    set y := (Basis.ofVectorSpace (ZMod 2) G).equivFun.toLinearMap.toAddMonoidHom;
    -- Since $x \neq 0$, there exists an index $i$ such that $y(x)(i) = 1$ by definition of $y$.
    -- In particular, there exists an index $i$ such that $repr x i = 1$.
    obtain ⟨i, hi⟩ : ∃ i : Basis.ofVectorSpaceIndex (ZMod 2) G, (y x : _) i = 1 := by
      have h_exists_i : ∃ i, (Basis.ofVectorSpace (ZMod 2) G).repr x i ≠ 0 := by
        contrapose! hx
        apply Basis.ofVectorSpace (ZMod 2) G |> Basis.ext_elem
        simp [hx]
      exact h_exists_i.imp fun _ hi ↦ (Fin.exists_fin_two.mp <| by simp).resolve_left hi
    -- Define $f : G →+ ZMod 2$ by $f(z) = y(z)(i)$ for all $z \in G$.
    set f : G →+ ZMod 2 := (Pi.evalAddMonoidHom (fun _ => ZMod 2) i).comp y
    exact ⟨f, hi⟩
  -- By definition of $y$, we know that $y$ is a bijection between the set of additive characters
  -- that map $x$ to 1 and the set of additive characters that map $x$ to 0.
  apply Nat.card_congr
  refine Equiv.ofBijective (⟨· - y, by aesop⟩) ⟨fun _ ↦ by aesop, fun ⟨b, hb⟩ ↦ ?_⟩;
  rw [Subtype.exists]
  use b + y
  aesop

theorem card_of_slice (A : Set G) :
    ∃ φ : G →+ ZMod 2, 2*Nat.card { x | x ∈ A ∧ φ x = 1 } ≥ (Nat.card A-1) := by
  classical
  have _ : Fintype (G →+ ZMod 2) := Fintype.ofEquiv G dual_iso.toEquiv
  have h1 := calc
        2 * ∑ φ : G →+ ZMod 2, Nat.card {x | x ∈ A ∧ φ x = 1}
    _ = 2 * ∑ φ : G →+ ZMod 2, ∑ x ∈ A, if φ x = 1 then 1 else 0 := by
      congr 1; apply Finset.sum_congr rfl; intro φ _
      simp [Fintype.subtype_card]; congr 1
      aesop
    _ = 2*∑ x ∈ A, Nat.card { φ : G →+ ZMod 2 | φ x = 1 } := by
      congr 1; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      simp [Fintype.subtype_card]
    _ ≥ 2*∑ x ∈ (A.toFinset.erase 0), Nat.card { φ : G →+ ZMod 2 | φ x = 1 } := by
      by_cases h : 0 ∈ A
      · rw [←Finset.sum_erase_add (s := A.toFinset) (a := 0)]
        · simp
        simp [h]
      apply le_of_eq
      congr
      apply Finset.erase_eq_of_notMem
      simp [h]
    _ = ∑ x ∈ (A.toFinset.erase 0), Nat.card G := by
      rw [Finset.mul_sum]
      congr! with x hx
      simp only [mem_erase, ne_eq, Set.mem_toFinset] at hx
      exact card_of_dual_constrained x hx.1
    _ ≥ (Nat.card A-1) * (Nat.card G) := by
      simp only [sum_const, smul_eq_mul, ge_iff_le, Nat.card_eq_card_toFinset]
      gcongr
      exact Finset.pred_card_le_card_erase
    _ = Nat.card G * (Nat.card A-1)  := by ring
  by_contra! h2
  replace h2 :
      2*∑ φ : G →+ ZMod 2, Nat.card {x | x ∈ A ∧ φ x = 1} < ∑ φ : G →+ ZMod 2, (Nat.card A-1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty
    · simp
    intro φ _; exact h2 φ
  simp only [sum_const, card_univ, smul_eq_mul,←Nat.card_eq_fintype_card,card_of_dual] at h2
  order

theorem approx_hom_pfr' (f : G → G') (K : ℝ) (hK : K > 0)
    (hf : Nat.card G ^ 2 / K ≤ Nat.card {x : G × G | f (x.1 + x.2) = f x.1 + f x.2}) :
    ∃ (φ'' : G →+ G'), Nat.card {x | f x = φ'' x} ≥ (Nat.card G / (2 ^ 144 * K ^ 122) - 1)/2 := by
    obtain ⟨ φ, c, h ⟩ := approx_hom_pfr f K hK hf
    set A := { x | f x = φ x + c }
    obtain ⟨ φ', h' ⟩ := card_of_slice A
    let φ'c : G →+ G' := {
      toFun x := (φ' x) • c
      map_add' := by intros; simp [add_smul]
      map_zero' := by simp
    }
    use φ + φ'c
    rw [ge_iff_le, div_le_iff₀ (by norm_num)]
    calc
      _ ≤ Nat.card A - (1:ℝ) := by gcongr
      _ ≤ (Nat.card ↑A - 1:ℕ) := by norm_cast; convert Int.le_natCast_sub _ _; norm_cast
      _ ≤ 2 * Nat.card ↑{x | x ∈ A ∧ φ' x = 1} := by norm_cast
      _ ≤ _ := by
        rw [mul_comm]; gcongr
        apply Nat.card_mono
        · apply Set.toFinite
        intro x
        simp only [Set.mem_setOf_eq, AddMonoidHom.add_apply, AddMonoidHom.coe_mk,
          ZeroHom.coe_mk, and_imp, A, φ'c]
        intro h1 h2
        simp [h1, h2]

#print axioms approx_hom_pfr'
