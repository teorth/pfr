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

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSingletonClass G]
 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {X : Ω → G} {Y : Ω' → G} {μ: Measure Ω} {μ': Measure Ω'}
[IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- If $G$ is torsion-free and $X,Y$ are $G$-valued random variables then $d[X;2Y]\leq 5d[X;Y]$.  -/
proof_wanted torsion_free_doubling (hG : AddMonoid.IsTorsionFree G) :
  d[X ; μ # (Y + Y) ; μ'] ≤ 5 * d[X; μ # Y ; μ']

/-- If $G$ is a torsion-free group and $X,Y$ are $G$-valued random variables and
$\phi:G\to \mathbb{F}_2^d$ is a homomorphism then
\[\mathbb{H}(\phi(X))\leq 10d[X;Y].\] -/
proof_wanted torsion_dist_shrinking {H : Type*} [AddCommGroup H] [ElementaryAddCommGroup H 2]
  [Fintype H] [MeasurableSpace H] (hG : AddMonoid.IsTorsionFree G) (φ : G →+ H) :
  H[φ ∘ X ; μ] ≤ 10 * d[X; μ # Y ; μ']

end Torsion

section F2_projection

open Real ProbabilityTheory MeasureTheory

variable {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]
 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {X : Ω → G} {Y : Ω' → G} {μ: Measure Ω} {μ': Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

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
proof_wanted PFR_projection :  ∃ H : AddSubgroup G, log (Nat.card H) < 2 * (H[X; μ] + H[Y;μ']) ∧ H[ (QuotientAddGroup.mk' H) ∘ X; μ ] + H[ (QuotientAddGroup.mk' H) ∘ Y; μ' ] < 44 * d[X;μ # Y;μ']

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

variable {G : Type*} [AddCommGroup G] [Module ℤ G] [Module.Free ℤ G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

open Real MeasureTheory ProbabilityTheory Pointwise

lemma weak_PFR_asymm_prelim {A B : Set G} [Finite A] [Finite B] [Nonempty A] [Nonempty B] {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω'] {UA : Ω → G} {UB : Ω' → G} [IsProbabilityMeasure (ℙ:Measure Ω)] [IsProbabilityMeasure (ℙ:Measure Ω')] (hUA: IsUniform A UA) (hUB: IsUniform B UB): ∃ (N : AddSubgroup G) (x y : G ⧸ N) (Ax By : Set G) (Ωx Ωy : Type*) (hΩx:MeasureSpace Ωx) (hΩy:MeasureSpace Ωy) (UAx: Ωx → G) (UBy: Ωy → G), Nonempty Ax ∧ Nonempty By ∧ Ax = {z:G | z ∈ A ∧ QuotientAddGroup.mk' N z = x } ∧ By = {z:G | z ∈ B ∧ QuotientAddGroup.mk' N z = y } ∧ IsProbabilityMeasure (ℙ:Measure Ωx) ∧IsProbabilityMeasure (ℙ:Measure Ωy)  ∧ IsUniform Ax UAx ∧ IsUniform By UBy ∧ (log 2) * FiniteDimensional.finrank ℤ G ≤ log (Nat.card (G ⧸ N)) + 40 * d[ UA # UB ] ∧ log (Nat.card A) + log (Nat.card B) - log (Nat.card Ax) - log (Nat.card By) ≤ 44 * (d[ UA # UB ] - d[ UAx # UBy ]) := by
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
