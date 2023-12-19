import Mathlib.Tactic.Rify
import PFR.EntropyPFR

/-!
# Weak PFR over the integers

Here we use the entropic form of PFR to deduce a weak form of PFR over the integers.

## Main statement

* `weak_PFR_int`: Let $A\subseteq \mathbb{Z}^d$ and $\lvert A+A\rvert\leq K\lvert A\rvert$. There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-48}\lvert A\rvert$ and $\dim A' \leq 60\log K$.

-/


/-- If $G$ is torsion-free and $X,Y$ are $G$-valued random variables then $d[X;2Y]\leq 5d[X;Y]$.  -/
proof_wanted torsion_free_doubling : 0 = 1

/-- If $G$ is a torsion-free group and $X,Y$ are $G$-valued random variables and $\phi:G\to \mathbb{F}_2^d$ is a homomorphism then
\[\mathbb{H}(\phi(X))\leq 10d[X;Y].\] -/
proof_wanted torsion_dist_shrinking : 0 = 1

section F2_projection

open Real ProbabilityTheory MeasureTheory

variable {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G]  [MeasurableSingletonClass G]
 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {X : Ω → G} {Y : Ω' → G} {μ: Measure Ω} {μ': Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- Let $G=\mathbb{F}_2^n$ and $X,Y$ be $G$-valued random variables such that
\[\mathbb{H}(X)+\mathbb{H}(Y)> 48d[X;Y].\]
There is a non-trivial subgroup $H\leq G$ such that
\[\log \lvert H\rvert <\mathbb{H}(X)+\mathbb{H}(Y)\] and
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))< \frac{\mathbb{H}(X)+\mathbb{H}(Y)}{2}\]
where $\psi:G\to G/H$ is the natural projection homomorphism.
-/
proof_wanted app_ent_PFR (hent: H[ X; μ] + H[Y; μ'] > 48 * d[X;μ # Y;μ']): ∃ H : AddSubgroup G, log (Nat.card H) < H[X; μ] + H[Y;μ'] ∧ H[ (QuotientAddGroup.mk' H) ∘ X; μ ] + H[ (QuotientAddGroup.mk' H) ∘ Y; μ' ] < (H[ X; μ] + H[Y; μ'])/2

/-- If $G=\mathbb{F}_2^d$ and $X,Y$ are $G$-valued random variables then there is a subgroup $H\leq \mathbb{F}_2^d$ such that
\[\log \lvert H\rvert \leq 2(\mathbb{H}(X)+\mathbb{H}(Y))\]
and if $\psi:G \to G/H$ is the natural projection then
\[\mathbb{H}(\psi(X))+\mathbb{H}(\psi(Y))\leq 48 d[\psi(X);\psi(Y)].\] -/
proof_wanted PFR_projection :  ∃ H : AddSubgroup G, log (Nat.card H) < 2 * (H[X; μ] + H[Y;μ']) ∧ H[ (QuotientAddGroup.mk' H) ∘ X; μ ] + H[ (QuotientAddGroup.mk' H) ∘ Y; μ' ] < 48 * d[X;μ # Y;μ']

end F2_projection

open MeasureTheory ProbabilityTheory Real

/-- Let $\phi:G\to H$ be a homomorphism and $A,B\subseteq G$ be finite subsets. If $x,y\in H$ then let $A_x=A\cap \phi^{-1}(x)$ and $B_y=B\cap \phi^{-1}(y)$. There exist $x,y\in H$ such that $A_x,B_y$ are both non-empty and
\[d[\phi(U_A);\phi(U_B)]\log \frac{\lvert A\rvert\lvert B\rvert}{\lvert A_x\rvert\lvert B_y\rvert}\leq (\mathbb{H}(\phi(U_A))+\mathbb{H}(\phi(U_B)))(d(U_A,U_B)-d(U_{A_x},U_{B_y}).\] -/
proof_wanted single_fibres {G H Ω Ω': Type*} [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
[AddCommGroup H] [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]
  (φ : G →+ H) {A B: Set G} [Finite A] [Finite B] [Nonempty A] [Nonempty B] [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ: Measure Ω} {μ': Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] {UA : Ω → G} {UB: Ω' → G} (hUA': Measurable UA) (hUB': Measurable UB) (hUA: IsUniform A UA μ) (hUB: IsUniform B UB μ') : ∃ (x y : H) (Ax By: Set G) (Ωx Ωy : Type*) (hΩx:MeasurableSpace Ωx) (hΩy:MeasurableSpace Ωy) (μx:Measure Ωx) (μy:Measure Ωy) (UAx: Ωx → G) (UBy: Ωy → G), Ax = A ∩ φ⁻¹' {x} ∧ By = B ∩ φ⁻¹' {y} ∧ Nonempty Ax ∧ Nonempty By ∧ IsProbabilityMeasure μx ∧ IsProbabilityMeasure μy ∧ Measurable UAx ∧ Measurable UBy ∧ IsUniform Ax UAx μx ∧ IsUniform By UBy μy ∧ d[ φ ∘ UA; μ # φ ∘ UB; μ' ] * log ((Nat.card A) * (Nat.card B) / ( (Nat.card Ax) * (Nat.card By)) ) ≤ (H[ φ ∘ UA; μ ] + H[ φ ∘ UB; μ' ]) * (d[ UA; μ # UB; μ' ] - d[ UAx; μx # UBy; μy ])

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

/-- If $A,B\subseteq \mathbb{Z}^d$ are finite non-empty sets then there exist non-empty $A'\subseteq A$ and $B'\subseteq B$ such that
\[\log\frac{\lvert A\rvert\lvert B\rvert}{\lvert A'\rvert\lvert B'\rvert}\leq 48d[U_A;U_B]\]
such that $\max(\dim A',\dim B')\leq \frac{40}{\log 2} d[U_A;U_B]$. -/
proof_wanted weak_PFR_asymm (A B : Set G) [Finite A] [Finite B] [Nonempty A] [Nonempty B] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {UA : Ω → G} {UB : Ω' → G} {μ: Measure Ω} {μ': Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hUA: IsUniform A UA μ) (hUB: IsUniform B UB μ'): ∃ A' B' : Set G, A' ⊆ A ∧ B' ⊆ B ∧ Nonempty A' ∧ Nonempty B' ∧ log (((Nat.card A) * (Nat.card B)) / ((Nat.card A') * (Nat.card B'))) ≤ 48 * d[UA; μ # UB; μ'] ∧ max (dimension A') (dimension B') ≤ (40 / log 2) * d[UA; μ # UB; μ']

/-- If $A\subseteq \mathbb{Z}^d$ is a finite non-empty set with $d[U_A;U_A]\leq \log K$ then there exists a non-empty $A'\subseteq A$ such that
\[\lvert A'\rvert\geq K^{-48}\lvert A\rvert\]
and $\dim A'\leq 60\log K$. -/
proof_wanted weak_PFR (A : Set G) [Finite A]  [Nonempty A] {Ω : Type*} [MeasurableSpace Ω] {UA : Ω → G} {μ: Measure Ω} [IsProbabilityMeasure μ] (hUA: IsUniform A UA μ) (K : ℝ) (hK: 0 < K) (hdist: d[UA; μ # UA ; μ] ≤ log K): ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-48 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ 60 * log K

/-- Let $A\subseteq \mathbb{Z}^d$ and $\lvert A+A\rvert\leq K\lvert A\rvert$. There exists $A'\subseteq A$ such that $\lvert A'\rvert \geq K^{-48}\lvert A\rvert$ and $\dim A' \leq 60\log K$.-/
proof_wanted weak_PFR_int (A : Set G) [Finite A]  [Nonempty A] (K : ℝ) (hK: 0 < K) (hA: Nat.card (A+A) ≤ K * Nat.card A) : ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-48 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ 60 * log K
