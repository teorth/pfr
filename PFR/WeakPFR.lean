import PFR.EntropyPFR
import PFR.ForMathlib.Entropy.RuzsaSetDist
import Mathlib.GroupTheory.Torsion
import Mathlib.Algebra.Quotient
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Weak PFR over the integers

Here we use the entropic form of PFR to deduce a weak form of PFR over the integers.

## Main statement

* `weak_PFR_int`: Let $A\subseteq \mathbb{Z}^d$ and $\lvert A+A\rvert\leq K\lvert A\rvert$. There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-44}\lvert A\rvert$ and $\dim A' \leq 60\log K$.

-/

section Torsion

open Real ProbabilityTheory MeasureTheory

variable {G : Type u} [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
 {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G) (μ: Measure Ω := by volume_tac) (μ': Measure Ω' := by volume_tac)
[IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- If $G$ is torsion-free and $X,Y$ are $G$-valued random variables then $d[X;2Y]\leq 5d[X;Y]$.  -/
proof_wanted torsion_free_doubling (hG : AddMonoid.IsTorsionFree G) :
  d[X ; μ # (Y + Y) ; μ'] ≤ 5 * d[X; μ # Y ; μ']

/-- If $G$ is a torsion-free group and $X,Y$ are $G$-valued random variables and
$\phi:G\to \mathbb{F}_2^d$ is a homomorphism then
\[\mathbb{H}(\phi(X))\leq 10d[X;Y].\] -/
lemma torsion_dist_shrinking {H : Type u} [AddCommGroup H] [ElementaryAddCommGroup H 2]
  [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] (hG : AddMonoid.IsTorsionFree G) (φ : G →+ H) :
  H[φ ∘ X ; μ] ≤ 10 * d[X; μ # Y ; μ'] := by sorry

end Torsion

section F2_projection

open Real ProbabilityTheory MeasureTheory

variable {G : Type u} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
 {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G) (μ: Measure Ω := by volume_tac) (μ': Measure Ω' := by volume_tac) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- Let $G=\mathbb{F}_2^n$ and $X,Y$ be $G$-valued random variables such that
\[\mathbb{H}(X)+\mathbb{H}(Y)> 44d[X;Y].\]
There is a non-trivial subgroup $H\leq G$ such that
\[\log \lvert H\rvert <\mathbb{H}(X)+\mathbb{H}(Y)\] and
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))< \frac{\mathbb{H}(X)+\mathbb{H}(Y)}{2}\]
where $\psi:G\to G/H$ is the natural projection homomorphism.
-/
proof_wanted app_ent_PFR (hent: H[ X; μ] + H[Y; μ'] > 44 * d[X;μ # Y;μ']): ∃ H : AddSubgroup G, log (Nat.card H) < H[X; μ] + H[Y;μ'] ∧ H[ (QuotientAddGroup.mk' H) ∘ X; μ ] + H[ (QuotientAddGroup.mk' H) ∘ Y; μ' ] < (H[ X; μ] + H[Y; μ'])/2

/-- If $G=\mathbb{F}_2^d$ and $X,Y$ are $G$-valued random variables then there is a subgroup $H\leq \mathbb{F}_2^d$ such that
\[\log \lvert H\rvert \leq 2(\mathbb{H}(X)+\mathbb{H}(Y))\]
and if $\psi:G \to G/H$ is the natural projection then
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))\leq 44 d[\psi(X);\psi(Y)].\] -/
lemma PFR_projection :  ∃ H : AddSubgroup G, log (Nat.card H) ≤ 2 * (H[X; μ] + H[Y;μ']) ∧ H[ (QuotientAddGroup.mk' H) ∘ X; μ ] + H[ (QuotientAddGroup.mk' H) ∘ Y; μ' ] ≤ 44 * d[(QuotientAddGroup.mk' H) ∘ X;μ # (QuotientAddGroup.mk' H) ∘ Y;μ'] := by sorry

end F2_projection

open MeasureTheory ProbabilityTheory Real

lemma four_logs {a b c d : ℝ} (ha: 0 < a) (hb: 0 < b) (hc: 0 < c) (hd: 0 < d) : log ((a*b)/(c*d)) = (log a) + (log b) - (log c) - (log d) := calc log ((a*b)/(c*d))
  _  = log (a*b) - log (c*d) := by rw [log_div (by positivity) (by positivity)]
  _ = log a + log b - log (c*d) := by rw [log_mul (by positivity) (by positivity)]
  _ = log a + log b - (log c + log d) := by rw [log_mul (by positivity) (by positivity)]
  _ = log a + log b - log c - log d := by ring

/-- Let $\phi:G\to H$ be a homomorphism and $A,B\subseteq G$ be finite subsets. If $x,y\in H$ then let $A_x=A\cap \phi^{-1}(x)$ and $B_y=B\cap \phi^{-1}(y)$. There exist $x,y\in H$ such that $A_x,B_y$ are both non-empty and
\[d[\phi(U_A);\phi(U_B)]\log \frac{\lvert A\rvert\lvert B\rvert}{\lvert A_x\rvert\lvert B_y\rvert}\leq (\mathbb{H}(\phi(U_A))+\mathbb{H}(\phi(U_B)))(d(U_A,U_B)-d(U_{A_x},U_{B_y}).\] -/
lemma single_fibres {G H Ω Ω': Type u} [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
[AddCommGroup H] [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]
  (φ : G →+ H) {A B: Set G} [Finite A] [Finite B] [Nonempty A] [Nonempty B] [MeasureSpace Ω] [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ:Measure Ω)] [IsProbabilityMeasure  (ℙ:Measure Ω')] {UA : Ω → G} {UB: Ω' → G} (hUA': Measurable UA) (hUB': Measurable UB) (hUA: IsUniform A UA) (hUB: IsUniform B UB) : ∃ (x y : H) (Ax By: Set G), Ax = A ∩ φ⁻¹' {x} ∧ By = B ∩ φ⁻¹' {y} ∧ Nonempty Ax ∧ Nonempty By  ∧ d[ φ ∘ UA # φ ∘ UB ] * log ((Nat.card A) * (Nat.card B) / ( (Nat.card Ax) * (Nat.card By)) ) ≤ (H[ φ ∘ UA ] + H[ φ ∘ UB ]) * (d[ UA # UB ] - dᵤ[ Ax # By ]) := by sorry

section dim

open Classical TensorProduct

variable {G : Type u} [AddCommGroup G]

/-- If $A\subseteq \mathbb{Z}^{d}$ then by $\dim(A)$ we mean the dimension of the span of $A-A$
  over the reals -- equivalently, the smallest $d'$ such that $A$ lies in a coset of a subgroup
  isomorphic to $\mathbb{Z}^{d'}$. -/
noncomputable def dimension (A : Set G) : ℕ := Set.finrank ℝ
  ((fun (n : G) => (1 : ℝ) ⊗ₜ n) '' A : Set (ℝ ⊗[ℤ] G))

lemma dimension_le_finset_card (A : Finset G) : dimension (A : Set G) ≤ A.card := by
  rw [dimension, Finset.coe_image.symm]
  apply le_trans (finrank_span_finset_le_card _) Finset.card_image_le

proof_wanted dimension_ne_zero [Module.Free ℤ G] (A : Set G) (hA : A ≠ ⊥) : dimension A ≠ 0

/- If G ≅ ℤᵈ then there is a subgroup H of G such that A lies in a coset of H. This is helpful to
  give the equivalent definition of `dimension`. Here this is stated in greated generality since the
  proof carries over automatically-/
lemma exists_coset_cover (A : Set G) :
  ∃ (d : ℕ), ∃ (S : Submodule ℤ G) (v : G), FiniteDimensional.finrank ℤ S = d ∧ ∀ a ∈ A, a - v ∈ S := by
  existsi FiniteDimensional.finrank ℤ (⊤ : Submodule ℤ G), ⊤, 0
  refine ⟨rfl, fun a _ ↦ trivial⟩

noncomputable def dimension' (A : Set G) : ℕ := Nat.find (exists_coset_cover A)

lemma dimension'_le_of_coset_cover (A : Set G) (S : Submodule ℤ G) (v : G)
  (hA : ∀ a ∈ A, a - v ∈ S) : dimension' A ≤ FiniteDimensional.finrank ℤ S := by
  apply Nat.find_le
  existsi S , v
  exact ⟨rfl, hA⟩

lemma dimension_eq_dimension' [Module.Free ℤ G] [Module.Finite ℤ G] (A : Set G) : dimension A = dimension' A := by sorry

lemma dimension_le_rank [Module.Finite ℤ G] (A : Set G) :
  dimension A ≤ FiniteDimensional.finrank ℤ G := by sorry

end dim

variable {G : Type u} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

open Real MeasureTheory ProbabilityTheory Pointwise

/-- Move to Mathlib? `Finsupp.mapRange` of a surjective function is surjective. -/
lemma Finsupp.mapRange_surjective {α : Type u_1} {M : Type u_5} {N : Type u_7} [Zero M] [Zero N] (f : M → N) (hf : f 0 = 0)
  (hs: Function.Surjective f) : Function.Surjective (Finsupp.mapRange (α := α) f hf) := by
  classical
  let g (n : N) : M := if n = 0 then 0 else Function.surjInv hs n
  have : Function.RightInverse g f := by
    intro n
    by_cases h : n = 0
    . simp [h,hf]
    simp [h, Function.surjInv_eq hs n]
  have hg : g 0 = 0 := by simp
  have hfg : (f ∘ g) 0 = 0 := by simp [hf, hg]
  intro F
  use Finsupp.mapRange g hg F
  rw [<-Finsupp.mapRange_comp (h:=hfg)]
  convert Finsupp.mapRange_id F
  convert Function.RightInverse.id this

/-- A free Z-module is torsion-free. Move to Mathlib? -/
lemma torsion_free : AddMonoid.IsTorsionFree G := by
    rintro x hx hn
    rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hn
    rcases hn with ⟨ n, hn, hn' ⟩
    apply_fun Module.Free.repr ℤ G at hn'
    simp_rw [map_nsmul, map_zero, smul_eq_zero, AddEquivClass.map_eq_zero_iff, hx, or_false] at hn'
    linarith

/-- If G is a rank n free Z-module, then G/2G is a finite elementary 2-group of cardinality 2^n.  Code is slow, needs to be golfed -/
lemma weak_PFR_quotient_prelim :
  let H := G ⧸ (AddMonoidHom.range (zsmulAddGroupHom 2))
  ElementaryAddCommGroup H 2 ∧ Finite H ∧ Nat.card H = 2^(FiniteDimensional.finrank ℤ G) := by
  set ψ : G →+ G := zsmulAddGroupHom 2
  set G₂ := AddMonoidHom.range ψ
  set H := G ⧸ G₂
  set φ : G →+ H := QuotientAddGroup.mk' G₂
  have hH_elem : ElementaryAddCommGroup H 2 := by
    apply ElementaryAddCommGroup.quotient_group (by decide)
    intro x; rw [AddMonoidHom.mem_range]
    use x
    rw [zsmulAddGroupHom_apply]
    norm_cast
  let B := Module.Free.ChooseBasisIndex ℤ G
  let bG : Basis B ℤ G := Module.Free.chooseBasis ℤ G
  have hB_fin : Fintype B := by infer_instance
  have hB_card : Nat.card B = FiniteDimensional.finrank ℤ G := by
    rw [FiniteDimensional.finrank_eq_card_basis bG, Nat.card_eq_fintype_card]
  have hH_module : Module (ZMod 2) H := by infer_instance
  let mod : (B →₀ ℤ) →+ (B →₀ ZMod 2) := Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod 2))
  let f : G →+ (B →₀ ℤ) := bG.repr
  have hker : G₂ ≤ AddMonoidHom.ker (AddMonoidHom.comp mod f) := by
    intro x hx
    simp_rw [AddMonoidHom.mem_range, zsmulAddGroupHom_apply, AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, Int.coe_castAddHom] at hx ⊢
    rcases hx with ⟨ y, rfl⟩
    ext b
    simp_rw [map_zsmul, Finsupp.mapRange_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      Int.cast_mul, Int.int_cast_ofNat, Finsupp.coe_zero, Pi.zero_apply, mul_eq_zero]
    left
    exact ZMod.nat_cast_self 2
  let g : H →+ (B →₀ ZMod 2) := QuotientAddGroup.lift G₂ (AddMonoidHom.comp mod f) hker
  have hsur : Function.Surjective g := by
    have h1 : Function.Surjective mod := Finsupp.mapRange_surjective (Int.castAddHom (ZMod 2)) (map_zero _) ZMod.int_cast_surjective
    have h2 := h1.comp bG.repr.surjective
    have h3 : mod ∘ bG.repr = g ∘ (QuotientAddGroup.mk' G₂) := by
      ext x b
      simp only [Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, Int.coe_castAddHom,
        Finsupp.mapRange_apply, QuotientAddGroup.coe_mk', QuotientAddGroup.lift_mk,
        AddMonoidHom.coe_comp, AddMonoidHom.coe_coe]
    rw [h3] at h2
    apply Function.Surjective.of_comp h2
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rcases QuotientAddGroup.mk'_surjective G₂ x with ⟨y, rfl⟩
    simp_rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, Int.coe_castAddHom,FunLike.ext_iff,Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply,ZMod.int_cast_zmod_eq_zero_iff_dvd] at hx
    replace hx := fun x ↦ Int.mul_ediv_cancel' (hx x)
    let z (b:B) := ((Module.Free.chooseBasis ℤ G).repr y) b / 2
    let z' := (Finsupp.equivFunOnFinite).symm z
    change ∀ b:B, 2 * z' b = (f y) b at hx
    let x' := bG.repr.symm z'
    simp_rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range, zsmulAddGroupHom_apply]
    use x'
    change 2 • (bG.repr.symm.toLinearMap.toAddMonoidHom z') = y
    rw [<-AddMonoidHom.map_zsmul bG.repr.symm.toLinearMap.toAddMonoidHom z' (2:ℤ)]
    rw [<- LinearEquiv.symm_apply_apply bG.repr y]
    change bG.repr.symm (2 • z') = bG.repr.symm (f y)
    congr
    ext b
    rw [Finsupp.smul_apply, <-hx b, smul_eq_mul]
  rcases Function.bijective_iff_has_inverse.mp ⟨ hinj, hsur ⟩ with ⟨ g', hg' ⟩

  have bH : Basis B (ZMod 2) H := by
    constructor
    exact {
      toFun := g
      invFun := g'
      left_inv := hg'.1
      right_inv := hg'.2
      map_add' := AddMonoidHom.map_add _
      map_smul' := by
        intro r x
        rcases ZMod.int_cast_surjective r with ⟨ n, rfl ⟩
        change g ((n:ZMod 2) • x) = (n:ZMod 2) • g x
        rw [intCast_smul, intCast_smul]
        exact AddMonoidHom.map_zsmul g x n
    }
  have hH_fin : Fintype H := Module.fintypeOfFintype bH
  have hH_card : Nat.card H = 2^(FiniteDimensional.finrank ℤ G) := by
    rw [Nat.card_eq_fintype_card, Module.card_fintype bH, <- Nat.card_eq_fintype_card (α := B), hB_card]
    congr
  exact ⟨ hH_elem, Finite.of_fintype H, hH_card ⟩

open QuotientAddGroup

/-- A version of the third isomorphism theorem: if G₂ ≤ G and H' is a subgroup of G⧸G₂, then there is a canonical isomorphism between H⧸H' and G⧸N, where N is the preimage of H' in G. A bit clunky; may be a better way to do this -/
lemma third_iso {G : Type u} [AddCommGroup G] {G₂: AddSubgroup G} (H': AddSubgroup (G ⧸ G₂)) :
  let H := G ⧸ G₂
  let φ : G →+ H := mk' G₂
  let N := AddSubgroup.comap φ H'
  ∃ e : H ⧸ H' ≃+ G ⧸ N, ∀ x : G, e (mk' H' (φ x))= mk' N x := by
  set H := G ⧸ G₂
  let φ : G →+ H := mk' G₂
  let N := AddSubgroup.comap φ H'
  have h1 : G₂ ≤ N := by
    intro x hx
    rw [<-eq_zero_iff] at hx
    simp [hx, AddSubgroup.zero_mem H']
  set H'' := AddSubgroup.map (mk' G₂) N
  have h2 : H' = H'' := by
    change H' = AddSubgroup.map (mk' G₂) N
    rw [AddSubgroup.map_comap_eq, AddMonoidHom.range_top_of_surjective _ (mk'_surjective G₂)]
    simp
  let e1 : H ⧸ H'' ≃+ G ⧸ N := quotientQuotientEquivQuotient _ _ h1
  let e2 := quotientAddEquivOfEq h2
  set e := e2.trans e1
  use e
  intro x
  convert (quotientQuotientEquivQuotientAux_mk_mk _ _ h1 x) using 1

lemma single {Ω: Type u} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] (μ: Measure Ω) [IsProbabilityMeasure μ] {A: Set Ω} {z:Ω} (hA: μ.real A = 1) (hz: μ.real {z} > 0) : z ∈ A := by
  contrapose! hz
  have : Disjoint {z} A := by simp [hz]
  replace this := measureReal_union (μ := μ) this (measurableSet_discrete _)
  simp [hA] at this
  have h := measureReal_mono (μ := μ) (show insert z A ⊆ Set.univ by simp)
  simp [this] at h
  assumption

/-- Given two non-empty finite subsets A, B of a rank n free Z-module G, there exists a subgroup N and points x, y in G/N such that the fibers Ax, By of A, B over x, y respectively are non-empty, one has the inequality
$$ \log \frac{|A| |B|}{|A_x| |B_y|} ≤ 44 (d[U_A; U_B] - d[U_{A_x}; U_{B_y}])$$
and one has the dimension bound
$$ n \log 2 ≤ \log |G/N| + 40 d[U_A; U_B].$$
 -/
lemma weak_PFR_asymm_prelim (A B : Set G) [Finite A] [Finite B] [hnA: Nonempty A] [hnB: Nonempty B]: ∃ (N : AddSubgroup G) (x y : G ⧸ N) (Ax By : Set G), Nonempty Ax ∧ Nonempty By ∧ Set.Finite Ax ∧ Set.Finite By ∧ Ax = {z:G | z ∈ A ∧ QuotientAddGroup.mk' N z = x } ∧ By = {z:G | z ∈ B ∧ QuotientAddGroup.mk' N z = y } ∧ (log 2) * FiniteDimensional.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) + 40 * dᵤ[ A # B ] ∧ log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By) ≤ 44 * (dᵤ[ A # B ] - dᵤ[ Ax # By ]) := by
  obtain ⟨ h_elem, h_finite, h_card ⟩ := weak_PFR_quotient_prelim (G := G)
  set ψ : G →+ G := zsmulAddGroupHom 2
  set G₂ := AddMonoidHom.range ψ
  set H := G ⧸ G₂
  let φ : G →+ H := QuotientAddGroup.mk' G₂
  let _mH : MeasurableSpace H := ⊤
  have _msH : MeasurableSingletonClass H := ⟨λ _ ↦ trivial⟩
  have h_fintype : Fintype H := Fintype.ofFinite H
  have h_torsionfree := torsion_free (G := G)

  obtain ⟨ Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, hUA_fin ⟩ := exists_isUniform_measureSpace' A
  obtain ⟨ Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, hUB_fin ⟩ := exists_isUniform_measureSpace' B

  rcases (PFR_projection (φ.toFun ∘ UA) (φ.toFun ∘ UB) ℙ ℙ) with ⟨H', ⟨ hH1, hH2 ⟩ ⟩
  let N := AddSubgroup.comap φ H'
  set φ' := QuotientAddGroup.mk' N
  have _cGN : Countable (G ⧸ N) := Function.Surjective.countable (QuotientAddGroup.mk'_surjective N)
  have _msGN : MeasurableSingletonClass (G ⧸ N) := by
    constructor
    intro x
    exact MeasurableSpace.map_def.mpr (measurableSet_discrete _)

  rcases third_iso H' with ⟨ e : H ⧸ H' ≃+ G ⧸ N, he ⟩
  rcases single_fibres φ' hUA_mes hUB_mes hUA_unif hUB_unif with ⟨x, y, Ax, By, hAx, hBy, hnAx, hnBy, hcard_ineq⟩

  have Axf : Finite Ax := by rw [hAx]; infer_instance
  have Byf : Finite By := by rw [hBy]; infer_instance

  have h1 := torsion_dist_shrinking UA UB ℙ ℙ h_torsionfree φ
  have h2 := torsion_dist_shrinking UB UA ℙ ℙ h_torsionfree φ
  rw [rdist_symm] at h2
  rw [<- rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes] at h1 h2
  -- using explicit .toFun casts as this saves a lot of heartbeats
  change H[φ.toFun ∘ UA] ≤ 10 * dᵤ[A # B] at h1
  change H[φ.toFun ∘ UB] ≤ 10 * dᵤ[A # B] at h2
  replace hH1 : log (Nat.card H') ≤ 40  * dᵤ[A # B] := by
    apply hH1.trans
    linarith
  replace h_card : (log 2) * FiniteDimensional.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) + 40 * dᵤ[A # B] := by
    rw [mul_comm, <- log_rpow (by norm_num)]
    norm_cast
    classical
    rwa [<-h_card, <- Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, <-AddSubgroup.index_mul_card H', AddSubgroup.index_eq_card, Nat.cast_mul, log_mul, add_le_add_iff_left, <-Nat.card_eq_fintype_card]
    all_goals norm_cast; exact Fintype.card_ne_zero


  use N, x, y, Ax, By
  refine ⟨ hnAx, hnBy, Ax.toFinite, By.toFinite, hAx, hBy, h_card, ?_ ⟩

  replace hH2 : H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB] ≤ 44 * d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] := by
    set X := ((mk' H').toFun ∘ φ.toFun) ∘ UA
    set Y := ((mk' H').toFun ∘ φ.toFun) ∘ UB
    have hX : Measurable X := Measurable.comp (measurable_discrete _) hUA_mes
    have hY : Measurable Y := Measurable.comp (measurable_discrete _) hUB_mes
    change H[X] + H[Y] ≤ 44 * d[X # Y] at hH2

    have ha : φ'.toFun ∘ UA = e.toFun ∘ X := by ext x; exact (he (UA x)).symm
    have hb : φ'.toFun ∘ UB = e.toFun ∘ Y := by ext x; exact (he (UB x)).symm
    have he_inj : Function.Injective e.toFun := AddEquiv.injective e
    rw [ha, hb, entropy_comp_of_injective _ hX _ he_inj, entropy_comp_of_injective _ hY _ he_inj]
    have : d[e.toFun ∘ X # e.toFun ∘ Y] = d[X # Y] :=  rdist_of_inj hX hY e.toAddMonoidHom he_inj
    rwa [this]

  set X : Ω → G ⧸ N := φ'.toFun ∘ UA
  set Y : Ω' → G ⧸ N := φ'.toFun ∘ UB
  have hX : Measurable X := Measurable.comp (measurable_discrete _) hUA_mes
  have hY : Measurable Y := Measurable.comp (measurable_discrete _) hUB_mes
  rcases le_iff_lt_or_eq.mp (rdist_nonneg (μ := ℙ) (μ' := ℙ) hX hY) with h | h
  swap
  . rw [<-h] at hH2
    have hH2A : H[X] ≥ 0 := entropy_nonneg _ _
    have hH2B : H[Y] ≥ 0 := entropy_nonneg _ _
    have hH2A' : H[X] ≤ 0 := by linarith only [hH2, hH2A, hH2B]
    have hH2B' : H[Y] ≤ 0 := by linarith only [hH2, hH2A, hH2B]

    rcases const_of_nonpos_entropy (μ := ℙ) hX hH2A' with ⟨ x', hx ⟩
    rcases const_of_nonpos_entropy (μ := ℙ) hY hH2B' with ⟨ y', hy ⟩

    have hAAx {z:G} (hz: z ∈ A) : φ'.toFun z = x' := by
      change (ℙ).real (UA⁻¹' (φ'⁻¹' {x'})) = 1 at hx
      rw [<-MeasureTheory.map_measureReal_apply hUA_mes (measurableSet_discrete _)] at hx
      set Af := A.toFinite.toFinset
      have hUAf : IsUniform Af UA := by
        convert hUA_unif; simp only [Set.Finite.coe_toFinset]
      have hnAf: Nat.card Af > 0 := by simp only [Set.Finite.mem_toFinset, gt_iff_lt, Nat.card_pos]
      have hzf: z ∈ Af := by simp [Set.Finite.mem_toFinset, hz]
      have : (Measure.map UA ℙ).real {z} > 0 := by
        rw [IsUniform.measureReal_preimage_of_mem' hUAf hUA_mes hzf]
        positivity
      have _ : IsProbabilityMeasure ((ℙ).map UA) := by
        exact MeasureTheory.isProbabilityMeasure_map (Measurable.aemeasurable hUA_mes)
      replace this := single ((ℙ).map UA) hx this
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this

    have hxx : Ax = A := by
      have h : (Classical.choice hnAx).val ∈ Ax := Subtype.mem _
      simp [hAx] at h ⊢
      have := hAAx h.1
      simp [h.2] at this
      intro z hz
      simp [this]
      convert hAAx hz

    have hBBy {z:G} (hz: z ∈ B) : φ'.toFun z = y' := by
      change (ℙ).real (UB⁻¹' (φ'⁻¹' {y'})) = 1 at hy
      rw [<-MeasureTheory.map_measureReal_apply hUB_mes (measurableSet_discrete _)] at hy
      set Bf := B.toFinite.toFinset
      have hUBf : IsUniform Bf UB := by convert hUB_unif; simp only [Set.Finite.coe_toFinset]
      have hnBf: Nat.card Bf > 0 := by simp only [Set.Finite.mem_toFinset, gt_iff_lt, Nat.card_pos]
      have hzf: z ∈ Bf := by simp [Set.Finite.mem_toFinset, hz]
      have : (Measure.map UB ℙ).real {z} > 0 := by
        rw [IsUniform.measureReal_preimage_of_mem' hUBf hUB_mes hzf]
        positivity
      have _ : IsProbabilityMeasure ((ℙ).map UB) := by
        exact MeasureTheory.isProbabilityMeasure_map (Measurable.aemeasurable hUB_mes)
      replace this := single ((ℙ).map UB) hy this
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this

    have hyy : By = B := by
      have h : (Classical.choice hnBy).val ∈ By := Subtype.mem _
      simp [hBy] at h ⊢
      have := hBBy h.1
      simp [h.2] at this
      intro z hz
      simp [this]
      convert hBBy hz

    simp [hxx, hyy]

  have := calc d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By))
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * log ((Nat.card A) * (Nat.card B) / ((Nat.card Ax) * (Nat.card By))) := by
      congr
      convert (four_logs ?_ ?_ ?_ ?_).symm
      all_goals norm_cast; exact Nat.card_pos
    _ ≤ (H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := hcard_ineq
    _ ≤ (44 * d[φ'.toFun ∘ UA # φ'.toFun ∘ UB]) * (d[UA # UB] - dᵤ[Ax # By]) := by
      apply mul_le_mul_of_nonneg_right hH2
      have := rdist_le_avg_ent (Measurable.comp (measurable_discrete φ'.toFun) hUA_mes) (Measurable.comp (measurable_discrete φ'.toFun) hUB_mes)
      replace this : 0 < H[φ'.toFun ∘ UA] + H[φ'.toFun ∘ UB] := by linarith
      rw [<-mul_le_mul_left this]
      apply le_trans _ hcard_ineq
      rw [mul_zero]
      change 0 ≤ d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * log ((Nat.card A) * (Nat.card B) / ((Nat.card Ax) * (Nat.card By)))
      rw [<- mul_zero d[φ'.toFun ∘ UA # φ'.toFun ∘ UB], mul_le_mul_left h]
      apply Real.log_nonneg
      rw [one_le_div]
      gcongr
      . apply Nat.card_mono
        . exact Set.toFinite A
        rw [hAx]; exact Set.inter_subset_left _ _
      apply Nat.card_mono
      . exact Set.toFinite B
      rw [hBy]; exact Set.inter_subset_left _ _
      norm_cast
      exact mul_pos Nat.card_pos Nat.card_pos
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (44 * (d[UA # UB] - dᵤ[Ax # By])) := by ring
    _ = d[φ'.toFun ∘ UA # φ'.toFun ∘ UB] * (44 * (dᵤ[A # B] - dᵤ[Ax # By])) := by rw [<- rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes]
  exact (mul_le_mul_left h).mp this

/-- Separting out the conclusion of `weak_PFR_asymm` for convenience of induction arguments.-/
def weak_PFR_asymm_conclusion (A B : Set G) : Prop := ∃ A' B' : Set G, A' ⊆ A ∧ B' ⊆ B ∧ Nonempty A' ∧ Nonempty B' ∧ log (((Nat.card A) * (Nat.card B)) / ((Nat.card A') * (Nat.card B'))) ≤ 44 * dᵤ[A # B] ∧ max (dimension A') (dimension B') ≤ (40 / log 2) * dᵤ[A # B]

/-- The property of two sets A,B of a group G not being contained in cosets of the same proper subgroup -/
def not_in_coset {G: Type u} [AddCommGroup G] (A B : Set G) : Prop := AddSubgroup.closure ((A-A) ∪ (B-B)) = ⊤

def is_shift {G: Type u} [AddCommGroup G] {H: AddSubgroup G} (A : Set G) (A' : Set H) : Prop := ∃ x, A = (A' : Set G) + {x}

lemma sub_of_shift  {G: Type u} [AddCommGroup G] {H: AddSubgroup G} {A : Set G} {A' : Set H} (hA: is_shift A A') : A - A = (A' - A': Set H) := by
  rcases hA with ⟨ x, hA ⟩
  ext z; constructor
  . intro hz
    rw [hA, Set.mem_sub] at hz
    rcases hz with ⟨ a1, a2, ha1, ha2, ha12 ⟩
    rw [Set.add_singleton, Set.image_add_right, Set.mem_preimage, Set.mem_image] at ha1 ha2
    rcases ha1 with ⟨ a1', ha1', ha1 ⟩
    rcases ha2 with ⟨ a2', ha1', ha2 ⟩
    have : z = (a1' - a2':H) := by push_cast; rw [ha1, ha2, <-ha12]; abel
    rw [this]
    convert Set.mem_image_of_mem Subtype.val ?_
    rw [Set.mem_sub]
    use a1', a2'
  intro hz
  rw [Set.mem_image] at hz
  rcases hz with ⟨ z', hz, hzz ⟩
  rw [Set.mem_sub] at hz
  rcases hz with ⟨ a1, a2, ha1, ha2, ha12 ⟩
  rw [Set.mem_sub, <-hzz, <-ha12, hA]
  use a1+x, a2+x
  simp [ha1, ha2]

lemma card_of_shift  {G: Type u} [AddCommGroup G] {H: AddSubgroup G} {A : Set G} {A' : Set H} (hA: is_shift A A') [Finite A] [Nonempty A] : Finite A' ∧ Nonempty A' ∧ Nat.card A' = Nat.card A := by
  rcases hA with ⟨ x, hA ⟩
  set f : H → G := fun a ↦ (a:G) + x
  have hf : Function.Injective f := by
    intro y z hyz
    simp at hyz
    exact hyz
  have hA' : A = f '' A' := by
    rw [hA]
    ext a
    simp_rw [Set.add_singleton, Set.mem_image]
    constructor
    . rintro ⟨ a', ⟨ b, hb, hb' ⟩, ha ⟩
      use b; rw [<-hb'] at ha; exact ⟨ hb, ha ⟩
    rintro ⟨ a', ha, ha' ⟩
    use a'; refine ⟨?_, ha' ⟩
    use a'
  have hA'_card : Nat.card A' = Nat.card A := by
    rw [hA', Nat.card_image_of_injective hf]
  have hA'_nonfin : Nonempty A' ∧ Finite A' := by
    have := Nat.card_pos (α := A)
    rw [<-hA'_card, Nat.card_pos_iff] at this
    exact this
  exact ⟨ hA'_nonfin.2, hA'_nonfin.1, hA'_card ⟩



/-- Without loss of generality, one can move (up to translation and embedding) any pair A, B of non-empty sets into a subgroup where they are not in a coset. -/
lemma wlog_not_in_coset {G: Type u} [AddCommGroup G] (A B : Set G) [hA: Nonempty A] [hB: Nonempty B] : ∃ (G': AddSubgroup G) (A' B' : Set G'), is_shift A A' ∧ is_shift B B' ∧ not_in_coset A' B' := by
  set G' := AddSubgroup.closure ((A-A) ∪ (B-B))
  obtain ⟨ x ⟩ := hA
  obtain ⟨ y ⟩ := hB
  set A' : Set G' := { a : G' | (a:G) + x ∈ A }
  set B' : Set G' := { b : G' | (b:G) + y ∈ B }
  use G', A', B'
  have hA : is_shift A A' := by
    use x; ext z; simp
    intro hz
    apply AddSubgroup.subset_closure
    rw [Set.mem_union]; left
    rw [Set.mem_sub]
    use z, x
    refine ⟨ hz, Subtype.mem x, sub_eq_add_neg z x ⟩
  have hB : is_shift B B' := by
    use y; ext z; simp
    intro hz
    apply AddSubgroup.subset_closure
    rw [Set.mem_union]; right
    rw [Set.mem_sub]
    use z, y
    refine ⟨ hz, Subtype.mem y, sub_eq_add_neg z y ⟩

  refine ⟨ hA, hB, ?_ ⟩
  unfold not_in_coset
  rw [AddSubgroup.eq_top_iff']
  intro z
  rw [AddSubgroup.mem_closure]
  intro K hK
  replace hK := Set.image_mono (f := Subtype.val) hK
  rw [Set.image_union] at hK
  change ((A'-A':Set G'):Set G) ∪ ((B'-B':Set G'):Set G) ⊆ (K:Set G') at hK
  rw [<-sub_of_shift hA, <-sub_of_shift hB, <- AddSubgroup.coeSubtype, <-AddSubgroup.coe_map (AddSubgroup.subtype G') K, <-AddSubgroup.closure_le] at hK
  change G' ≤ AddSubgroup.map (AddSubgroup.subtype G') K at hK
  replace hK := hK (SetLike.coe_mem z)
  simp at hK
  exact hK

/-- In fact one has equality here, but this is tricker to prove and not needed for the argument. -/
lemma dimension_of_shift {G: Type u} [AddCommGroup G]  [Module.Free ℤ G] [Module.Finite ℤ G] {H: AddSubgroup G} [Module.Free ℤ H] [Module.Finite ℤ H] (A : Set H) (x : G) : dimension ((fun a:H ↦ (a:G) + x) '' A) ≤ dimension A := by
  rw [dimension_eq_dimension', dimension_eq_dimension']
  classical
  rcases Nat.find_spec (exists_coset_cover A) with ⟨ S, v, hrank, hshift ⟩
  change FiniteDimensional.finrank ℤ S = dimension' A at hrank
  rw [<-hrank]
  convert dimension'_le_of_coset_cover _ (Submodule.map H.subtype.toIntLinearMap S) (x+v) ?_
  . apply LinearEquiv.finrank_eq
    exact Submodule.equivMapOfInjective _ (by simpa using Subtype.val_injective) _
  intro a ha
  rw [Set.mem_image] at ha
  rcases ha with ⟨ b, ⟨ hb, hb'⟩ ⟩
  rw [Submodule.mem_map]
  use b - v, hshift b hb
  simp [<-hb']
  abel

lemma conclusion_transfers {A B : Set G} [Finite A] [Finite B] [Nonempty A] [Nonempty B] (G': AddSubgroup G) [Module.Finite ℤ G'] [Module.Free ℤ G'] (A' B' : Set G') (hA: is_shift A A') (hB: is_shift B B') [Finite A'] [Finite B'] [Nonempty A'] [Nonempty B'] : weak_PFR_asymm_conclusion A' B' → weak_PFR_asymm_conclusion A B := by
  intro this
  rcases this with ⟨ A'', B'', hA'', hB'', hA''_non, hB''_non, hcard_ineq, hdim_ineq ⟩
  rcases hA with ⟨ x, hA ⟩
  set f : G' → G := fun a ↦ (a:G) + x
  have hf : Function.Injective f := by
    intro y z hyz
    simp at hyz
    exact hyz
  have hA' : A = f '' A' := by
    rw [hA]
    ext a
    simp_rw [Set.add_singleton, Set.mem_image]
    constructor
    . rintro ⟨ a', ⟨ b, hb, hb' ⟩, ha ⟩
      use b; rw [<-hb'] at ha; exact ⟨ hb, ha ⟩
    rintro ⟨ a', ha, ha' ⟩
    use a'; refine ⟨?_, ha' ⟩
    use a'
  rcases hB with ⟨ y, hB ⟩
  set g : G' → G := fun a ↦ (a:G) + y
  have hg : Function.Injective g := by
    intro y z hyz
    simp at hyz
    exact hyz
  have hB' : B = g '' B' := by
    rw [hB]
    ext a
    simp_rw [Set.add_singleton, Set.mem_image]
    constructor
    . rintro ⟨ a', ⟨ b, hb, hb' ⟩, ha ⟩
      use b; rw [<-hb'] at ha; exact ⟨ hb, ha ⟩
    rintro ⟨ a', ha, ha' ⟩
    use a'; refine ⟨?_, ha' ⟩
    use a'
  use f '' A'', g '' B''
  have : dᵤ[A # B] = dᵤ[A' # B'] := by
    rw [<-rdist_set_of_inj _ _ (φ := G'.subtype) Subtype.val_injective, <-rdist_set_add_const (G'.subtype '' A') (G'.subtype '' B') x y]
    congr

  refine ⟨ ?_, ?_, (by infer_instance), (by infer_instance), ?_, ?_ ⟩
  . simp [hA', hf, hA'']
  . simp [hB', hg, hB'']
  . convert hcard_ineq using 2
    . congr 3
      . rw [hA', Nat.card_image_of_injective hf]
      . rw [hB', Nat.card_image_of_injective hg]
      . rw [Nat.card_image_of_injective hf]
      rw [Nat.card_image_of_injective hg]
  convert LE.le.trans _ hdim_ineq using 2
  norm_cast
  apply max_le_max
  . exact dimension_of_shift A'' x
  exact dimension_of_shift B'' y


/-- If $A,B\subseteq \mathbb{Z}^d$ are finite non-empty sets then there exist non-empty $A'\subseteq A$ and $B'\subseteq B$ such that
\[\log\frac{\lvert A\rvert\lvert B\rvert}{\lvert A'\rvert\lvert B'\rvert}\leq 44d[U_A;U_B]\]
such that $\max(\dim A',\dim B')\leq \frac{40}{\log 2} d[U_A;U_B]$. -/
lemma weak_PFR_asymm (A B : Set G) [Finite A] [Finite B] [Nonempty A] [Nonempty B]: weak_PFR_asymm_conclusion A B  := by
  let P : ℕ → Prop := fun M ↦ (∀ (G : Type u) (hG_comm : AddCommGroup G) (_hG_free : Module.Free ℤ G) (_hG_fin : Module.Finite ℤ G) (_hG_count : Countable G) (hG_mes : MeasurableSpace G) (_hG_sing: MeasurableSingletonClass G) (A B: Set G) (_hA_fin: Finite A) (_hB_fin: Finite B) (_hA_non: Nonempty A) (_hB_non: Nonempty B) (_hM : (Nat.card A) + (Nat.card B) ≤ M), weak_PFR_asymm_conclusion A B)
  suffices : ∀ M, (∀ M', M' < M → P M') → P M
  . set M := (Nat.card A) + (Nat.card B)
    have hM : (Nat.card A) + (Nat.card B) ≤ M := Nat.le_refl _
    convert (Nat.strong_induction_on (p := P) M this) G ‹_› ‹_› ‹_› ‹_› _ ‹_› A B ‹_› ‹_› ‹_› ‹_› hM
  intro M h_induct
  -- wlog we can assume A, B are not in cosets of a smaller subgroup
  suffices : ∀ (G : Type u) (hG_comm : AddCommGroup G) (_hG_free : Module.Free ℤ G) (_hG_fin : Module.Finite ℤ G) (_hG_count : Countable G) (hG_mes : MeasurableSpace G) (_hG_sing: MeasurableSingletonClass G) (A B: Set G) (_hA_fin: Finite A) (_hB_fin: Finite B) (_hA_non: Nonempty A) (_hB_non: Nonempty B) (_hM : (Nat.card A) + (Nat.card B) ≤ M) (_hnot: not_in_coset A B), weak_PFR_asymm_conclusion A B
  . intro G hG_comm hG_free hG_fin hG_count hG_mes hG_sing A B hA_fin hB_fin hA_non hB_non hM

    obtain ⟨ G', A', B', hA, hB, hnot' ⟩ := wlog_not_in_coset A B
    have hG'_fin : Module.Finite ℤ G' :=
      (AddSubgroup.toIntSubmodule G').fg_iff_finite.mp (IsNoetherian.noetherian _)

    have hG'_free : Module.Free ℤ G' := by
      rcases Submodule.nonempty_basis_of_pid (Module.Free.chooseBasis ℤ G) (AddSubgroup.toIntSubmodule G') with ⟨ n, ⟨ b ⟩ ⟩
      exact Module.Free.of_basis b

    obtain ⟨ hA'_fin, hA'_non, hA'_card ⟩ := card_of_shift hA
    obtain ⟨ hB'_fin, hB'_non, hB'_card ⟩ := card_of_shift hB
    rw [<-hA'_card, <-hB'_card] at hM
    replace this := this G' _ hG'_free hG'_fin (by infer_instance) (by infer_instance) (by infer_instance) A' B' hA'_fin hB'_fin hA'_non hB'_non hM hnot'
    exact conclusion_transfers G' A' B' hA hB this
  intro G hG_comm hG_free hG_fin hG_count hG_mes hG_sing A B hA_fin hB_fin hA_non hB_non hM hnot
  rcases weak_PFR_asymm_prelim A B with ⟨ N, x, y, Ax, By, hAx_non, hBy_non, hAx_fin, hBy_fin, hAx, hBy, hdim, hcard⟩
  have hAxA : Ax ⊆ A := by rw [hAx]; simp
  have hByB : By ⊆ B := by rw [hBy]; simp
  have hA_pos : (0:ℝ) < Nat.card A := Nat.cast_pos.mpr Nat.card_pos
  have hB_pos : (0:ℝ) < Nat.card B := Nat.cast_pos.mpr Nat.card_pos

  rcases lt_or_ge (Nat.card Ax + Nat.card By) (Nat.card A + Nat.card B) with h | h
  . replace h := h_induct (Nat.card Ax + Nat.card By) (h.trans_le hM) G hG_comm hG_free hG_fin hG_count hG_mes hG_sing Ax By (Set.finite_coe_iff.mpr hAx_fin) (Set.finite_coe_iff.mpr hBy_fin) hAx_non hBy_non (Eq.le rfl)
    rcases h with ⟨ A', B', hA', hB', hA'_non, hB'_non, hcard_ineq, hdim_ineq ⟩
    use A', B'
    have hAx_fin' := Set.finite_coe_iff.mpr hAx_fin
    have hBy_fin' := Set.finite_coe_iff.mpr hBy_fin
    have hA'_fin' := Set.finite_coe_iff.mpr (Set.Finite.subset hAx_fin hA')
    have hB'_fin' := Set.finite_coe_iff.mpr (Set.Finite.subset hBy_fin hB')
    have hAx_pos : (0:ℝ) < Nat.card Ax := Nat.cast_pos.mpr Nat.card_pos
    have hBy_pos : (0:ℝ) < Nat.card By := Nat.cast_pos.mpr Nat.card_pos
    have hA'_pos : (0:ℝ) < Nat.card A' := Nat.cast_pos.mpr Nat.card_pos
    have hB'_pos : (0:ℝ) < Nat.card B' := Nat.cast_pos.mpr Nat.card_pos
    have hAxA_le : (Nat.card Ax:ℝ) ≤ (Nat.card A:ℝ) := Nat.cast_le.mpr (Nat.card_mono A.toFinite hAxA)
    have hByB_le : (Nat.card By:ℝ) ≤ (Nat.card B:ℝ) := Nat.cast_le.mpr (Nat.card_mono B.toFinite hByB)

    refine ⟨ hA'.trans hAxA, hB'.trans hByB, hA'_non, hB'_non, ?_, ?_ ⟩
    . rw [four_logs hA_pos hB_pos hA'_pos hB'_pos]
      rw [four_logs hAx_pos hBy_pos hA'_pos hB'_pos] at hcard_ineq
      linarith only [hcard, hcard_ineq]
    apply hdim_ineq.trans
    gcongr
    linarith only [Real.log_le_log hAx_pos hAxA_le, Real.log_le_log hBy_pos hByB_le, hcard]
  use A, B
  refine ⟨ Eq.subset rfl, Eq.subset rfl, hA_non, hB_non, ?_, ?_ ⟩
  . apply LE.le.trans _ <| mul_nonneg (by norm_num) <| rdist_set_nonneg A B
    rw [div_self (by positivity)]
    simp
  have hAx_eq : Ax = A := by
    apply Set.Finite.eq_of_subset_of_card_le A.toFinite hAxA
    linarith only [h, Nat.card_mono B.toFinite hByB]
  have hBy_eq : By = B := by
    apply Set.Finite.eq_of_subset_of_card_le B.toFinite hByB
    linarith only [h, Nat.card_mono A.toFinite hAxA]
  have hN : N = ⊤ := by
    have : (A-A) ∪ (B-B) ⊆ N := by
      rw [<-hAx_eq, <-hBy_eq, hAx, hBy]
      intro z hz
      simp [Set.mem_sub] at hz
      convert (QuotientAddGroup.eq_zero_iff z).mp ?_
      . infer_instance
      rcases hz with ⟨ a, ⟨ -, ha⟩, a', ⟨-, ha'⟩, haa' ⟩ | ⟨ b, ⟨ -, hb⟩, b', ⟨ -,hb'⟩, hbb' ⟩
      . rw [<-haa']; simp [ha, ha']
      rw [<-hbb']; simp [hb, hb']
    rw [<-AddSubgroup.closure_le, hnot] at this
    exact top_le_iff.mp this
  have : Nat.card (G ⧸ N) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    . rw [hN]
      exact  QuotientAddGroup.subsingleton_quotient_top
    infer_instance
  simp [this] at hdim
  rw [<-le_div_iff' (by positivity)] at hdim
  convert LE.le.trans ?_ hdim using 1
  . field_simp
  simp
  exact ⟨ dimension_le_rank A, dimension_le_rank B ⟩

/-- If $A\subseteq \mathbb{Z}^d$ is a finite non-empty set with $d[U_A;U_A]\leq \log K$ then there exists a non-empty $A'\subseteq A$ such that
$\lvert A'\rvert\geq K^{-22}\lvert A\rvert$
and $\dim A'\leq \frac{40}{\log 2} \log K$. -/
lemma weak_PFR {A : Set G} [Finite A]  [Nonempty A]  {K : ℝ} (hK: 0 < K) (hdist: dᵤ[A # A] ≤ log K): ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-22 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ (40 / log 2) * log K := by
  rcases weak_PFR_asymm A A with ⟨A', A'', hA', hA'', hA'nonempty, hA''nonempty, hcard, hdim⟩

  have : ∃ B : Set G, B ⊆ A ∧ (Nat.card B) ≥ (Nat.card A') ∧ (Nat.card B) ≥ (Nat.card A'') ∧ (dimension B) ≤
max (dimension A') (dimension A'') := by
    rcases lt_or_ge (Nat.card A') (Nat.card A'') with h | h
    . use A''
      exact ⟨hA'', by linarith, by linarith, le_max_right _ _⟩
    use A'
    exact ⟨hA', by linarith, by linarith, le_max_left _ _⟩

  rcases this with ⟨B, hB, hBcard, hBcard', hBdim⟩
  use B
  have hApos : Nat.card A > 0 := by
    rw [gt_iff_lt, Nat.card_pos_iff]
    exact ⟨ (by infer_instance), (by infer_instance) ⟩
  have hA'pos : Nat.card A' > 0 := by
    rw [gt_iff_lt, Nat.card_pos_iff]
    refine ⟨ (by infer_instance), Finite.Set.subset _ hA' ⟩
  have hA''pos : Nat.card A'' > 0 := by
    rw [gt_iff_lt, Nat.card_pos_iff]
    refine ⟨ (by infer_instance), Finite.Set.subset _ hA'' ⟩
  have hBpos : Nat.card B > 0 := by linarith

  refine ⟨hB, ?_, ?_⟩
  . have := calc 2 * log ((Nat.card A) / (Nat.card B))
      _ = log ( ((Nat.card A) * (Nat.card A)) / ((Nat.card B) * (Nat.card B)) ) := by
        convert (log_pow (((Nat.card A):ℝ)/(Nat.card B)) 2).symm
        field_simp
        rw [<-pow_two, <-pow_two]
      _ ≤ log ( ((Nat.card A) * (Nat.card A)) / ((Nat.card A') * (Nat.card A'')) ) := by
        apply log_le_log
        . positivity
        gcongr
      _ ≤ 44 * dᵤ[A # A] := hcard
      _ ≤ 44 * log K := mul_le_mul_of_nonneg_left hdist (by linarith)
      _ = 2 * (22 * log K) := by ring
      _ = 2 * log (K^22) := by
        congr
        convert (log_pow K 22).symm
    rw [mul_le_mul_left (by norm_num), log_le_log_iff (by positivity) (by positivity), div_le_iff (by positivity), <- mul_inv_le_iff (by positivity), <-ge_iff_le, mul_comm] at this
    convert this using 2
    convert zpow_neg K 22 using 1
    norm_cast
  calc ((dimension B) : ℝ)
    _ ≤ (((max (dimension A') (dimension A'')):ℕ):ℝ) := by norm_cast
    _ ≤ (40 / log 2) * dᵤ[A # A] := hdim
    _ ≤ (40 / log 2) * log K := mul_le_mul_of_nonneg_left hdist (by positivity)


/-- Let $A\subseteq \mathbb{Z}^d$ and $\lvert A-A\rvert\leq K\lvert A\rvert$. There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-22}\lvert A\rvert$ and $\dim A' \leq \frac{40}{\log 2} \log K$.-/
theorem weak_PFR_int {A : Set G} [Finite A]  [Nonempty A] {K : ℝ} (hK: 0 < K) (hA: Nat.card (A-A) ≤ K * Nat.card A) : ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-22 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ (40 / log 2) * log K := by
  apply weak_PFR hK ((rdist_set_le A A).trans _)
  suffices log (Nat.card (A-A)) ≤ log K + log (Nat.card A) by linarith
  rw [<-log_mul (by positivity) _]
  . apply log_le_log _ hA
    norm_cast
    have : Nonempty (A-A) := by
      have : Set.Nonempty A := Set.nonempty_coe_sort.mp ‹_›
      exact Set.Nonempty.coe_sort (Set.Nonempty.sub this this)
    apply Nat.card_pos
  norm_cast
  apply ne_of_gt Nat.card_pos
