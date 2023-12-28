import PFR.EntropyPFR
import PFR.Main
import Mathlib.GroupTheory.Torsion
import Mathlib.Algebra.Quotient

/-!
# Weak PFR over the integers

Here we use the entropic form of PFR to deduce a weak form of PFR over the integers.

## Main statement

* `weak_PFR_int`: Let $A\subseteq \mathbb{Z}^d$ and $\lvert A+A\rvert\leq K\lvert A\rvert$. There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-44}\lvert A\rvert$ and $\dim A' \leq 60\log K$.

-/

section Torsion

open Real ProbabilityTheory MeasureTheory

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G) (μ: Measure Ω := by volume_tac) (μ': Measure Ω' := by volume_tac)
[IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- If $G$ is torsion-free and $X,Y$ are $G$-valued random variables then $d[X;2Y]\leq 5d[X;Y]$.  -/
proof_wanted torsion_free_doubling (hG : AddMonoid.IsTorsionFree G) :
  d[X ; μ # (Y + Y) ; μ'] ≤ 5 * d[X; μ # Y ; μ']

/-- If $G$ is a torsion-free group and $X,Y$ are $G$-valued random variables and
$\phi:G\to \mathbb{F}_2^d$ is a homomorphism then
\[\mathbb{H}(\phi(X))\leq 10d[X;Y].\] -/
lemma torsion_dist_shrinking {H : Type*} [AddCommGroup H] [ElementaryAddCommGroup H 2]
  [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H] (hG : AddMonoid.IsTorsionFree G) (φ : G →+ H) :
  H[φ ∘ X ; μ] ≤ 10 * d[X; μ # Y ; μ'] := by sorry

end Torsion

section F2_projection

open Real ProbabilityTheory MeasureTheory

variable {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : Ω → G) (Y : Ω' → G) (μ: Measure Ω := by volume_tac) (μ': Measure Ω' := by volume_tac) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

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

/-- Let $\phi:G\to H$ be a homomorphism and $A,B\subseteq G$ be finite subsets. If $x,y\in H$ then let $A_x=A\cap \phi^{-1}(x)$ and $B_y=B\cap \phi^{-1}(y)$. There exist $x,y\in H$ such that $A_x,B_y$ are both non-empty and
\[d[\phi(U_A);\phi(U_B)]\log \frac{\lvert A\rvert\lvert B\rvert}{\lvert A_x\rvert\lvert B_y\rvert}\leq (\mathbb{H}(\phi(U_A))+\mathbb{H}(\phi(U_B)))(d(U_A,U_B)-d(U_{A_x},U_{B_y}).\] -/
proof_wanted single_fibres {G H Ω Ω': Type*} [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
[AddCommGroup H] [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]
  (φ : G →+ H) {A B: Set G} [Finite A] [Finite B] [Nonempty A] [Nonempty B] [MeasureSpace Ω] [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ:Measure Ω)] [IsProbabilityMeasure  (ℙ:Measure Ω')] {UA : Ω → G} {UB: Ω' → G} (hUA': Measurable UA) (hUB': Measurable UB) (hUA: IsUniform A UA) (hUB: IsUniform B UB) : ∃ (x y : H) (Ax By: Set G) (Ωx Ωy : Type*) (hΩx:MeasureSpace Ωx) (hΩy:MeasureSpace Ωy) (UAx: Ωx → G) (UBy: Ωy → G), Ax = A ∩ φ⁻¹' {x} ∧ By = B ∩ φ⁻¹' {y} ∧ Nonempty Ax ∧ Nonempty By ∧ IsProbabilityMeasure (ℙ:Measure Ωx) ∧ IsProbabilityMeasure (ℙ:Measure Ωy) ∧ Measurable UAx ∧ Measurable UBy ∧ IsUniform Ax UAx ∧ IsUniform By UBy ∧ d[ φ ∘ UA # φ ∘ UB ] * log ((Nat.card A) * (Nat.card B) / ( (Nat.card Ax) * (Nat.card By)) ) ≤ (H[ φ ∘ UA ] + H[ φ ∘ UB ]) * (d[ UA # UB ] - d[ UAx # UBy ])

section dim

open Classical TensorProduct

variable {G : Type*} [AddCommGroup G] [Module ℤ G]

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

proof_wanted dimension_eq_dimension' [Module.Free ℤ G] [Module.Finite ℤ G] (A : Set G) : dimension A = dimension' A

proof_wanted dimension_le_rank [Module.Finite ℤ G] (A : Set G) :
  dimension A ≤ FiniteDimensional.finrank ℤ G

end dim

variable {G : Type*} [AddCommGroup G] [Module ℤ G] [Module.Free ℤ G] [Module.Finite ℤ G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

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

#check PFR_projection

/-- Given two non-empty finite subsets A, B of a rank n free Z-module G, there exists a subgroup N and points x, y in G/N such that the fibers Ax, By of A, B over x, y respectively are non-empty, one has the inequality
$$ \log \frac{|A| |B|}{|A_x| |B_y|} ≤ 44 (d[U_A; U_B] - d[U_{A_x}; U_{B_y}])$$
and one has the dimension bound
$$ n \log 2 ≤ \log |G/N| + 40 d[U_A; U_B].$$
 -/
lemma weak_PFR_asymm_prelim {A B : Set G} [Finite A] [Finite B] [Nonempty A] [Nonempty B] {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω'] {UA : Ω → G} {UB : Ω' → G} [IsProbabilityMeasure (ℙ:Measure Ω)] [IsProbabilityMeasure (ℙ:Measure Ω')] (hUA: IsUniform A UA) (hUB: IsUniform B UB): ∃ (N : AddSubgroup G) (x y : G ⧸ N) (Ax By : Set G) (Ωx Ωy : Type*) (hΩx:MeasureSpace Ωx) (hΩy:MeasureSpace Ωy) (UAx: Ωx → G) (UBy: Ωy → G), Nonempty Ax ∧ Nonempty By ∧ Ax = {z:G | z ∈ A ∧ QuotientAddGroup.mk' N z = x } ∧ By = {z:G | z ∈ B ∧ QuotientAddGroup.mk' N z = y } ∧ IsProbabilityMeasure (ℙ:Measure Ωx) ∧IsProbabilityMeasure (ℙ:Measure Ωy)  ∧ IsUniform Ax UAx ∧ IsUniform By UBy ∧ (log 2) * FiniteDimensional.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) + 40 * d[ UA # UB ] ∧ log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By) ≤ 44 * (d[ UA # UB ] - d[ UAx # UBy ]) := by
  obtain ⟨ h_elem, h_finite, h_card ⟩ := weak_PFR_quotient_prelim (G := G)
  set ψ : G →+ G := zsmulAddGroupHom 2
  set G₂ := AddMonoidHom.range ψ
  set H := G ⧸ G₂
  let φ : G →+ H := QuotientAddGroup.mk' G₂
  let _mH : MeasurableSpace H := ⊤
  have _msH : MeasurableSingletonClass H := ⟨λ _ ↦ trivial⟩
  have h_fintype : Fintype H := Fintype.ofFinite H
  have h_torsionfree := torsion_free (G := G)
  rcases (PFR_projection (φ ∘ UA) (φ ∘ UB) ℙ ℙ) with ⟨H', ⟨ hH1, hH2 ⟩ ⟩
  replace hH1 : log (Nat.card H') ≤ 40  * d[UA # UB] := by
    apply hH1.trans
    have h1 := torsion_dist_shrinking UA UB ℙ ℙ h_torsionfree φ
    have h2 := torsion_dist_shrinking UB UA ℙ ℙ h_torsionfree φ
    rw [rdist_symm] at h2
    linarith
  
  sorry


/-- If $A,B\subseteq \mathbb{Z}^d$ are finite non-empty sets then there exist non-empty $A'\subseteq A$ and $B'\subseteq B$ such that
\[\log\frac{\lvert A\rvert\lvert B\rvert}{\lvert A'\rvert\lvert B'\rvert}\leq 44d[U_A;U_B]\]
such that $\max(\dim A',\dim B')\leq \frac{40}{\log 2} d[U_A;U_B]$. -/
lemma weak_PFR_asymm {A B : Set G} [Finite A] [Finite B] [Nonempty A] [Nonempty B] {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω'] {UA : Ω → G} {UB : Ω' → G} [IsProbabilityMeasure (ℙ: Measure Ω)] [IsProbabilityMeasure (ℙ: Measure Ω')] (hUA: IsUniform A UA) (hUB: IsUniform B UB): ∃ A' B' : Set G, A' ⊆ A ∧ B' ⊆ B ∧ Nonempty A' ∧ Nonempty B' ∧ log (((Nat.card A) * (Nat.card B)) / ((Nat.card A') * (Nat.card B'))) ≤ 44 * d[UA # UB] ∧ max (dimension A') (dimension B') ≤ (40 / log 2) * d[UA # UB] := by
  sorry

/-- If $A\subseteq \mathbb{Z}^d$ is a finite non-empty set with $d[U_A;U_A]\leq \log K$ then there exists a non-empty $A'\subseteq A$ such that
$\lvert A'\rvert\geq K^{-22}\lvert A\rvert$
and $\dim A'\leq \frac{40}{\log 2} \log K$. -/
lemma weak_PFR {A : Set G} [Finite A]  [Nonempty A] {Ω : Type*} [MeasureSpace Ω] {UA : Ω → G} [IsProbabilityMeasure (ℙ: Measure Ω)] (hUA: IsUniform A UA) {K : ℝ} (hK: 0 < K) (hdist: d[UA # UA] ≤ log K): ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-22 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ (40 / log 2) * log K := by
  rcases weak_PFR_asymm hUA hUA with ⟨A', A'', hA', hA'', hA'nonempty, hA''nonempty, hcard, hdim⟩

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
      _ ≤ 44 * d[UA # UA] := hcard
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
    _ ≤ (40 / log 2) * d[UA # UA] := hdim
    _ ≤ (40 / log 2) * log K := mul_le_mul_of_nonneg_left hdist (by positivity)


/-- Let $A\subseteq \mathbb{Z}^d$ and $\lvert A-A\rvert\leq K\lvert A\rvert$. There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-22}\lvert A\rvert$ and $\dim A' \leq \frac{40}{\log 2} \log K$.-/
theorem weak_PFR_int {A : Set G} [Finite A]  [Nonempty A] {K : ℝ} (hK: 0 < K) (hA: Nat.card (A-A) ≤ K * Nat.card A) : ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-22 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ (40 / log 2) * log K := by
  have hnonempty : Set.Nonempty A := Set.nonempty_coe_sort.mp (by infer_instance)
  set Af := A.toFinite.toFinset
  have : Af.Nonempty := by simp [hnonempty]
  rcases exists_isUniform_measureSpace Af this with ⟨Ω, mΩ, UA, hP, hmes, hunif, -⟩
  have hUA : IsUniform A UA := by
    convert hunif
    exact (Set.Finite.coe_toFinset (Set.toFinite A)).symm
  apply weak_PFR hUA hK _
  exact rdist_le_of_isUniform_of_card_add_le hnonempty hA hUA hmes
