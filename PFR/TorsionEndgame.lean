import PFR.BoundingMutual
import PFR.Main
import Mathlib.Data.Finset.Pointwise

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
local notation3 "Z3" => ∑ i: Fin p.m, ∑ j: Fin p.m, (-i-j:ℤ) • Y (i, j)
local notation3 "P" => fun i ↦ ∑ j, Y (i, j)
local notation3 "Q" => fun j ↦ ∑ i, Y (i, j)
local notation3 "R" => fun r ↦ ∑ i, ∑ j, if (i+j+r = 0) then Y r else 0


/--  Z_1+Z_2+Z_3= 0 -/
lemma sum_of_z_eq_zero :Z1 + Z2 + Z3 = 0 := by
  rw [<-Finset.sum_add_distrib, <-Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [<-Finset.sum_add_distrib, <-Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [<-add_zsmul, <-add_zsmul]
  convert zero_zsmul ?_
  simp

/--   We have `I[Z_1 : Z_2 | W], I[Z_2 : Z_3 | W], I[Z_1 : Z_3 | W] ≤  4m^2 η k`.
-/
lemma mutual_information_le_t_12 : I[ Z1 : Z2 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry

lemma mutual_information_le_t_13 : I[ Z1 : Z3 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry

lemma mutual_information_le_t_23 : I[ Z2 : Z3 | W] ≤ 4 * (p.m)^2 * p.η * k := sorry


/-- We have $\bbH[W] \leq (2m-1)k + \frac1m \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_W_le : H[W] ≤ (2*p.m - 1) * k + (m:ℝ)⁻¹ * ∑ i, H[X i] := sorry

/-- We have $\bbH[Z_2] \leq (8m^2-16m+1) k + \frac{1}{m} \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_Z_two_le : H[Z2] ≤ (8 * p.m^2 - 16 * p.m + 1) * k + (m:ℝ)⁻¹ * ∑ i, H[X i] := sorry

/-- We have  $\bbI[W : Z_2] \leq 2 (m-1) k$. -/
lemma mutual_of_W_Z_two_le : I[W : Z2] ≤ 2 * (p.m-1) * k := sorry

/-- We have $\sum_{i=1}^m d[X_i;Z_2|W] \leq 8(m^3-m^2) k$. -/
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

/-- We have $k = 0$. -/
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
lemma torsion_PFR_conjecture_aux {G : Type*} [AddCommGroup G] [Fintype G] {m:ℕ} (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (64 * m^3 + 2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card H ≤ K ^ (64 * m^3) * Nat.card A ∧ Nat.card A ≤ K ^ (64 * m^3) * Nat.card H ∧ A ⊆ c + H := sorry


-- A silly little set lemma
lemma set_avoid {G:Type*} {A B : Set G} (hA: A ⊆ B) (hneq: A ≠ B) : ∃ a:G, a ∈ B ∧ a ∉ A := by
  contrapose! hneq
  exact Set.Subset.antisymm hA hneq

open Pointwise

/-- Every subgroup H of a finite m-torsion abelian group G contains a subgroup H' of order between k and mk, if 0 < k < |H|. -/
lemma torsion_exists_subgroup_subset_card_le {G : Type*} {m : ℕ} (hm : m ≥ 2)
    [AddCommGroup G] [Fintype G] (htorsion: ∀ x:G, m • x = 0)
    {k : ℕ} (H : AddSubgroup G) (hk : k ≤ Nat.card H) (h'k : k ≠ 0) :
    ∃ (K : AddSubgroup G), Nat.card K ≤ k ∧ k < m * Nat.card K ∧ K ≤ H := by
    let S := {K: AddSubgroup G | K ≤ H ∧ Nat.card K ≤ k }
    have hnon : S.Nonempty := by
      use ⊥
      simp only [Set.mem_setOf_eq, bot_le, AddSubgroup.mem_bot, Nat.card_eq_fintype_card,
        Fintype.card_ofSubsingleton, true_and, S]
      exact Nat.one_le_iff_ne_zero.mpr h'k
    obtain ⟨ K, ⟨ hK, hK' ⟩ ⟩ := Set.Finite.exists_maximal_wrt (fun K:AddSubgroup G ↦ Nat.card K) S (Set.toFinite S) hnon
    simp only [ge_iff_le, Set.mem_setOf_eq, S] at hK
    use K
    refine ⟨ hK.2, ?_, hK.1 ⟩
    rcases LE.le.lt_or_eq hK.1 with heq | heq
    . have hneq : (K:Set G) ≠ (H:Set G) := by
        contrapose! heq
        simp only [SetLike.coe_set_eq] at heq
        simp only [heq, lt_self_iff_false, not_false_eq_true]
      obtain ⟨ a, ⟨ ha, ha' ⟩⟩ := set_avoid hK.1 hneq
      let Z := AddSubgroup.zmultiples a
      let H' := K ⊔ Z
      contrapose! ha'
      have hcard : Nat.card H' ≤ k := by
        apply le_trans _ ha'
        rw [<-SetLike.coe_sort_coe, <-SetLike.coe_sort_coe, AddSubgroup.normal_add K Z, Nat.mul_comm]
        calc
          _ ≤ (Nat.card (K:Set G)) * (Nat.card (Z:Set G)) := Set.card_add_le
          _ ≤ _ := by
            gcongr
            rw [SetLike.coe_sort_coe, Nat.card_zmultiples a]
            apply addOrderOf_le_of_nsmul_eq_zero (Nat.zero_lt_of_lt hm) (htorsion a)
      have hH' : H' ≤ H := by
        simpa only [sup_le_iff, hK.1, AddSubgroup.zmultiples_le, true_and, H', Z]
      have hsub : (K:Set G) ⊆ (H':Set G) := SetLike.coe_subset_coe.mpr le_sup_left
      have hcard' : Nat.card K ≤ Nat.card H' := by
          rw [<-SetLike.coe_sort_coe, <-SetLike.coe_sort_coe, Set.Nat.card_coe_set_eq (K:Set G), Set.Nat.card_coe_set_eq (H':Set G)]
          exact Set.ncard_le_ncard hsub (Set.toFinite H')
      have : (K:Set G) = (H':Set G) := by
          apply (Set.subset_iff_eq_of_ncard_le ?_ ?_).mp hsub
          . apply Eq.le
            rw [<-Set.Nat.card_coe_set_eq (H':Set G), <-Set.Nat.card_coe_set_eq (K:Set G)]
            exact ((hK' H' ⟨ hH', hcard ⟩) hcard').symm
          exact Set.toFinite (H':Set G)
      rw [this]
      exact (le_sup_right : AddSubgroup.zmultiples a ≤ H') (AddSubgroup.mem_zmultiples a)
    rw [heq]
    exact lt_of_le_of_lt hk ((Nat.lt_mul_iff_one_lt_left Nat.card_pos).mpr hm)







/--Suppose that $G$ is a finite abelian group of torsion $m$.
  If $A \subset G$ is non-empty and $|A+A| \leq K|A|$, then $A$ can be covered by most $mK^{64m^3+1}$ translates of a subspace $H$ of $G$ with $|H| \leq |A|$.
-/
theorem torsion_PFR  {G : Type*} [AddCommGroup G] [Fintype G] {m:ℕ} (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < m * K ^ (96*m^3+2) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K := PFR_conjecture_pos_aux' h₀A hA
   -- consider the subgroup `H` given by Lemma `torsion_PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (64 * m^3+2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card (H : Set G) ≤ K ^ (64*m^3) * Nat.card A ∧ Nat.card A ≤ K ^ (64*m^3) * Nat.card (H : Set G)
      ∧ A ⊆ c + H :=
    torsion_PFR_conjecture_aux hm htorsion h₀A hA

  have H_pos : (0 : ℝ) < Nat.card (H : Set G) := by
    have : 0 < Nat.card (H : Set G) := Nat.card_pos; positivity
  rcases le_or_lt (Nat.card (H : Set G)) (Nat.card A) with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ ((64*m^3+2)) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2) := hc
    _ ≤ K ^ ((64*m^3+2)) * (K ^ (64*m^3) * Nat.card (H : Set G)) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2) := by
      gcongr
    _ = K ^ (96*m^3+2) := by rpow_ring; norm_num; congr 1; ring
    _ < m * K ^ (96*m^3+2) := by
      apply (lt_mul_iff_one_lt_left _).mpr
      . norm_num; linarith [hm]
      positivity
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / m < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : AddSubgroup G, Nat.card (H' : Set G) ≤ Nat.card A
          ∧ Nat.card A < m * Nat.card (H' : Set G) ∧ H' ≤ H := by
      have A_pos' : 0 < Nat.card A := mod_cast A_pos
      exact torsion_exists_subgroup_subset_card_le hm htorsion H h.le A_pos'.ne'
    have : (Nat.card A / m : ℝ) < Nat.card (H' : Set G) := by
      rw [div_lt_iff, mul_comm]
      . norm_cast
      norm_cast; exact Nat.zero_lt_of_lt hm
    have H'_pos : (0 : ℝ) < Nat.card (H' : Set G) := by
      have : 0 < Nat.card (H' : Set G) := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ := AddSubgroup.exists_left_transversal_of_le H'H
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast Set.card_add_le
    _ ≤ (K ^ ((64*m^3+2)) * (Nat.card A) ^ (1 / 2) * (Nat.card (H : Set G) ^ (-1 / 2)))
          * (Nat.card (H : Set G) / Nat.card (H' : Set G)) := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ ((64*m^3+2)) * (Nat.card A) ^ (1 / 2) * (Nat.card (H : Set G) ^ (-1 / 2)))
          * (Nat.card (H : Set G) / (Nat.card A / m)) := by
        gcongr
    _ = m * K ^ ((64*m^3+2)) * (Nat.card A) ^ (-1/2) * (Nat.card (H : Set G)) ^ (1/2) := by
        have : (0 : ℝ) < Nat.card H := H_pos
        field_simp
        rpow_ring
        norm_num
    _ ≤ m * K ^ ((64*m^3+2)) * (Nat.card A) ^ (-1/2) * (K ^ (64*m^3) * Nat.card A) ^ (1/2) := by
        gcongr
    _ = m * K ^ (96*m^3+2) := by
        rpow_ring
        norm_num
        left; congr 1
        ring
