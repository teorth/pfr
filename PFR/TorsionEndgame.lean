import PFR.BoundingMutual


/-!
# Endgame for the Torsion PFR theorem


## Main definitions:


## Main results

-/

open MeasureTheory ProbabilityTheory BigOperators

variable (p: multiRefPackage) (Ω : Fin p.m → Type*) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → p.G) (hmin : multiTauMinimizes p Ω hΩ X)

local notation3 "k" => multiTau p Ω hΩ X

variable (Ω': Type*) [hΩ': MeasureSpace Ω'] (Y: Fin p.m × Fin p.m → Ω' → p.G) [IsFiniteMeasure hΩ'.volume] (hindep: iIndepFun (fun _ ↦ p.hGm) Y) (hident:
  let _ := p.hGm
  ∀ i, ∀ j, IdentDistrib (Y (i,j)) (X i) )

local notation3 "W" => ∑ i, ∑ j, Y (i, j)
local notation3 "Z1" => ∑ i: Fin p.m, ∑ j, (i:ℤ) • Y (i, j)
local notation3 "Z2" => ∑ i, ∑ j: Fin p.m, (j:ℤ) • Y (i, j)
local notation3 "Z3" => - ∑ i: Fin p.m, ∑ j: Fin p.m, (i+j:ℤ) • Y (i, j)
local notation3 "P" => fun i ↦ ∑ j, Y (i, j)
local notation3 "Q" => fun j ↦ ∑ i, Y (i, j)
local notation3 "R" => fun r ↦ ∑ i, ∑ j, if (i+j+r = 0) then Y r else 0


/--  Z_1+Z_2+Z_3= 0 -/
lemma sum_of_z_eq_zero :
 let _ := p.hG; Z1 + Z2 + Z3 = 0 := sorry

/--   We let
  \[
    \bbI[Z_1 : Z_2\, |\, W],\
    \bbI[Z_2 : Z_3\, |\, W],\
    \bbI[Z_1 : Z_3\, |\, W] \leq t
  \]
  where $t :=  4m^2 \eta k$.
-/
lemma mutual_information_le_t_12 : let _ := p.hG; let _ := p.hGm; I[ Z1 : Z2 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry

lemma mutual_information_le_t_13 : let _ := p.hG; let _ := p.hGm; I[ Z1 : Z3 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry

lemma mutual_information_le_t_23 : let _ := p.hG; let _ := p.hGm; I[ Z2 : Z3 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry


/-- We let $\bbH[W] \leq (2m-1)k + \frac1m \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_W_le : let _ := p.hG; let _ := p.hGm; H[W] ≤ (2*p.m - 1) * k + (m:ℝ)⁻¹ * ∑ i, H[X i] := sorry

/-- We let $\bbH[Z_2] \leq (8m^2-16m+1) k + \frac{1}{m} \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_Z_two_le : let _ := p.hG; let _ := p.hGm; H[Z2] ≤ (8 * p.m^2 - 16 * p.m + 1) * k + (m:ℝ)⁻¹ * ∑ i, H[X i] := sorry

/-- We let  $\bbI[W : Z_2] \leq 2 (m-1) k$. -/
lemma mutual_of_W_Z_two_le : let _ := p.hG; let _ := p.hGm; I[W : Z2] ≤ 2 * (p.m-1) * k := sorry

example : let hGm := p.hGm; @MeasurableSingletonClass p.G hGm := by
  let hGsc : @MeasurableSingletonClass p.G p.hGm := p.hGsc
  exact hGsc

/-- We let $\sum_{i=1}^m d[X_i;Z_2|W] \leq 8(m^3-m^2) k$. -/
lemma sum_of_conditional_distance_le : let _ := p.hG; let _ := p.hGm; let _ := p.hGsc; let _ := p.hGf; ∑ i, d[ X i # Z2 | W] ≤ 8 * (p.m^3 - p.m^2)*k := sorry


/-- Let $G$ be an abelian group, let $(T_1,T_2,T_3)$ be a $G^3$-valued random variable such that $T_1+T_2+T_3=0$ holds identically, and write
  \[
    \delta := \bbI[T_1 : T_2] + \bbI[T_1 : T_3] + \bbI[T_2 : T_3].
  \]
  Let $Y_1,\dots,Y_n$ be some further $G$-valued random variables and let $\alpha>0$ be a constant.
  Then there exists a random variable $U$ such that
$$    d[U;U] + \alpha \sum_{i=1}^n d[Y_i;U] \leq \Bigl(2 + \frac{\alpha n}{2} \Bigr) \delta + \alpha \sum_{i=1}^n d[Y_i;T_2].
$$
-/
lemma dist_of_U_add_le : 0 = 1 := sorry

/-- We let $k = 0$. -/
lemma k_eq_zero : k = 0 := sorry

/-- Suppose that $G$ is a finite abelian group of torsion $m$.  Suppose that $X$ is a $G$-valued random variable. Then there exists a subgroup $H \leq G$ such that \[ d[X;U_H] \leq 64 m^3 d[X;X].\] -/
lemma dist_of_X_U_H_le {G : Type*} [AddCommGroup G]  [Fintype G] [MeasurableSpace G]
  [MeasurableSingletonClass G] (m:ℕ) (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) (Ω: Type*) [MeasureSpace Ω] (X: Ω → G):  ∃ H : AddSubgroup G, ∃ Ω' : Type*, ∃ mΩ : MeasureSpace Ω', ∃ U : Ω' → G,
    IsUniform H U ∧ d[X # U] ≤ 64 * m^3 * d[X # X] := sorry


open Pointwise
/--Suppose that $G$ is a finite abelian group of torsion $m$.
  If $A \subset G$ is non-empty and $|A+A| \leq K|A|$, then $A$ can be covered by most $mK^{64m^3+1}$ translates of a subspace $H$ of $G$ with $|H| \leq |A|$.
-/
theorem torsion_PFR  {G : Type*} [AddCommGroup G] [Fintype G] (m:ℕ) (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < m * K ^ (64*m^3+1) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := sorry
