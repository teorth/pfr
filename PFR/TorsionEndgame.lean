import PFR.BoundingMutual


/-!
# Endgame for the Torsion PFR theorem


## Main definitions:


## Main results

-/

open MeasureTheory ProbabilityTheory BigOperators

section AnalyzeMinimizer

universe u

variable {G Ωₒ : Type u} [MeasureableFinGroup G] [MeasureSpace Ωₒ] (p : multiRefPackage G Ωₒ) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) (hmin : multiTauMinimizes p Ω hΩ X)

local notation3 "k" => multiTau p Ω hΩ X

variable (Ω': Type u) [hΩ': MeasureSpace Ω'] (Y: Fin p.m × Fin p.m → Ω' → G) [IsFiniteMeasure hΩ'.volume] (hindep: iIndepFun _ Y) (hident: ∀ i, ∀ j, IdentDistrib (Y (i,j)) (X i) )

local notation3 "W" => ∑ i, ∑ j, Y (i, j)
local notation3 "Z1" => ∑ i: Fin p.m, ∑ j, (i:ℤ) • Y (i, j)
local notation3 "Z2" => ∑ i, ∑ j: Fin p.m, (j:ℤ) • Y (i, j)
local notation3 "Z3" => - ∑ i: Fin p.m, ∑ j: Fin p.m, (i+j:ℤ) • Y (i, j)
local notation3 "P" => fun i ↦ ∑ j, Y (i, j)
local notation3 "Q" => fun j ↦ ∑ i, Y (i, j)
local notation3 "R" => fun r ↦ ∑ i, ∑ j, if (i+j+r = 0) then Y r else 0


/--  Z_1+Z_2+Z_3= 0 -/
lemma sum_of_z_eq_zero :Z1 + Z2 + Z3 = 0 := sorry

/--   We have `I[Z_1 : Z_2 | W], I[Z_2 : Z_3 | W], I[Z_1 : Z_3 | W] ≤  4m^2 η k`.
-/
lemma mutual_information_le_t_12 : I[ Z1 : Z2 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry

lemma mutual_information_le_t_13 : I[ Z1 : Z3 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry

lemma mutual_information_le_t_23 : I[ Z2 : Z3 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry


/-- We let $\bbH[W] \leq (2m-1)k + \frac1m \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_W_le : H[W] ≤ (2*p.m - 1) * k + (m:ℝ)⁻¹ * ∑ i, H[X i] := sorry

/-- We let $\bbH[Z_2] \leq (8m^2-16m+1) k + \frac{1}{m} \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_Z_two_le : H[Z2] ≤ (8 * p.m^2 - 16 * p.m + 1) * k + (m:ℝ)⁻¹ * ∑ i, H[X i] := sorry

/-- We let  $\bbI[W : Z_2] \leq 2 (m-1) k$. -/
lemma mutual_of_W_Z_two_le : I[W : Z2] ≤ 2 * (p.m-1) * k := sorry

/-- We let $\sum_{i=1}^m d[X_i;Z_2|W] \leq 8(m^3-m^2) k$. -/
lemma sum_of_conditional_distance_le : ∑ i, d[ X i # Z2 | W] ≤ 8 * (p.m^3 - p.m^2)*k := sorry


/-- Let $G$ be an abelian group, let $(T_1,T_2,T_3)$ be a $G^3$-valued random variable such that $T_1+T_2+T_3=0$ holds identically, and write
  \[
    \delta := \bbI[T_1 : T_2] + \bbI[T_1 : T_3] + \bbI[T_2 : T_3].
  \]
  Let $Y_1,\dots,Y_n$ be some further $G$-valued random variables and let $\alpha>0$ be a constant.
  Then there exists a random variable $U$ such that
$$    d[U;U] + \alpha \sum_{i=1}^n d[Y_i;U] \leq \Bigl(2 + \frac{\alpha n}{2} \Bigr) \delta + \alpha \sum_{i=1}^n d[Y_i;T_2].
$$
-/
lemma dist_of_U_add_le {G: Type*} [MeasureableFinGroup G] {Ω: Type*} [MeasureSpace Ω] (T₁ T₂ T₃ : Ω → G) (hsum: T₁ + T₂ + T₃ = 0) (n:ℕ) {Ω': Fin n → Type*} (hΩ': ∀ i, MeasureSpace (Ω' i)) (Y: ∀ i, (Ω' i) → G) {α:ℝ} (hα: α > 0): ∃ (Ω'':Type*) (hΩ'': MeasureSpace Ω'') (U: Ω'' → G), d[U # U] + α * ∑ i, d[Y i # U] ≤ (2 + α * n / 2) * (I[T₁ : T₂] + I[T₁ : T₃] + I[T₂ : T₃]) + α * ∑ i, d[Y i # T₂] := sorry

/-- We let $k = 0$. -/
lemma k_eq_zero : k = 0 := sorry

end AnalyzeMinimizer

local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))

/-- Suppose that $G$ is a finite abelian group of torsion $m$.  Suppose that $X$ is a $G$-valued random variable. Then there exists a subgroup $H \leq G$ such that \[ d[X;U_H] \leq 64 m^3 d[X;X].\] -/
lemma dist_of_X_U_H_le {G : Type*} [AddCommGroup G]  [Fintype G] [MeasurableSpace G]
  [MeasurableSingletonClass G] (m:ℕ) (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) (Ω: Type*) [MeasureSpace Ω] (X: Ω → G):  ∃ H : AddSubgroup G, ∃ Ω' : Type*, ∃ mΩ : MeasureSpace Ω', ∃ U : Ω' → G,
    IsUniform H U ∧ d[X # U] ≤ 64 * m^3 * d[X # X] := sorry


open Pointwise

/-- Suppose that $G$ is a finite abelian group of torsion $m$.  If $A \subset G$ is non-empty and
  $|A+A| \leq K|A|$, then $A$ can be covered by at most $K ^
  {(64m^3+2)/2}|A|^{1/2}/|H|^{1/2}$ translates of a subspace $H$ of $G$ with
 $|H|/|A| \in [K^{-64m^3}, K^{64m^3}]$
     -/
lemma torsion_PFR_conjecture_aux {G : Type*} [AddCommGroup G] [Fintype G] (m:ℕ) (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (64 * m^3 + 2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card H ≤ K ^ (64 * m^3) * Nat.card A ∧ Nat.card A ≤ K ^ (64 * m^3) * Nat.card H ∧ A ⊆ c + H := sorry


/--Suppose that $G$ is a finite abelian group of torsion $m$.
  If $A \subset G$ is non-empty and $|A+A| \leq K|A|$, then $A$ can be covered by most $mK^{64m^3+1}$ translates of a subspace $H$ of $G$ with $|H| \leq |A|$.
-/
theorem torsion_PFR  {G : Type*} [AddCommGroup G] [Fintype G] (m:ℕ) (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < m * K ^ (64*m^3+1) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := sorry
