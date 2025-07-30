import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators
import PFR.Main
import PFR.MultiTauFunctional
import PFR.BoundingMutual

/-!
# Endgame for the Torsion PFR theorem
-/

open MeasureTheory ProbabilityTheory Set
open scoped Pointwise

section AnalyzeMinimizer

universe u

variable {G Ωₒ : Type u} [MeasurableFinGroup G] [hΩ₀: MeasureSpace Ωₒ] {p : multiRefPackage G Ωₒ} {Ω : Fin p.m → Type u}
  (hΩ : ∀ i, MeasureSpace (Ω i)) {X : ∀ i, Ω i → G} (h_min : multiTauMinimizes p Ω hΩ X)
  (hΩ_prob : ∀ i, IsProbabilityMeasure (hΩ i).volume) (hX_mes: ∀ i, Measurable (X i))

local notation3 "k" => D[X; hΩ]

variable {Ω' : Type u} {Y : Fin p.m × Fin p.m → Ω' → G}

local notation3 "W" => ∑ i, ∑ j, Y (i, j)
local notation3 "Z1" => ∑ i: Fin p.m, ∑ j, (i:ℤ) • Y (i, j)
local notation3 "Z2" => ∑ i, ∑ j: Fin p.m, (j:ℤ) • Y (i, j)
local notation3 "Z3" => ∑ i: Fin p.m, ∑ j: Fin p.m, (-i-j:ℤ) • Y (i, j)
local notation3 "P" => fun i ↦ ∑ j, Y (i, j)
local notation3 "Q" => fun j ↦ ∑ i, Y (i, j)
local notation3 "R" => fun r ↦ ∑ i, ∑ j, if (i+j+r = 0) then Y r else 0

lemma Q_eq (j: Fin p.m) : Q j = ∑ i, Y (i, j) := by rfl

/-- Z_1+Z_2+Z_3= 0 -/
lemma sum_of_z_eq_zero :Z1 + Z2 + Z3 = 0 := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [← add_zsmul, ← add_zsmul]
  convert zero_zsmul ?_
  simp

variable [hΩ': MeasureSpace Ω'] [hΩ'_prob: IsProbabilityMeasure hΩ'.volume] (h_mes : ∀ i j, Measurable (Y (i, j)))
  (h_indep : iIndepFun Y) (hident : ∀ i j, IdentDistrib (Y (i, j)) (X i))

include h_mes h_indep in
omit hΩ'_prob in
lemma indep_yj (j : Fin p.m) : iIndepFun (fun i ↦ Y (i, j)) := by
  let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun i ↦ {(i,j)}
  let φ : (i:Fin p.m) → ((_: S i) → G) → G := fun i x ↦ x ⟨ (i,j), by simp [S] ⟩
  convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with i ω
  rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
  simp [S] at hij; cc

include h_mes h_indep hident h_min in
/-- We have `I[Z_1 : Z_2 | W], I[Z_2 : Z_3 | W], I[Z_1 : Z_3 | W] ≤ 4m^2 η k`.
-/
lemma mutual_information_le_t_12 : I[Z1 : Z2 | W] ≤ p.m * (4*p.m+1) * p.η * k := by
  have hm := p.hm
  let zero : Fin p.m := ⟨ 0, by linarith [hm]⟩
  have hindep_j (j: Fin p.m) : iIndepFun (fun i ↦ Y (i, j)) := indep_yj h_mes h_indep j
  have := mutual_information_le (by fun_prop) (hindep_j zero) ?_ h_mes h_indep ?_
  . have k_eq : k = D[fun i ω ↦ Y (i, zero) ω ; fun x ↦ hΩ'] := by
      apply multiDist_copy; intro i; exact (hident i zero).symm
    rw [←k_eq, condMutualInfo_comm] at this
    apply LE.le.trans _ this
    convert condMutual_comp_comp_le _ _ _ _ (fun (x: Fin p.m → G) ↦ ∑ i, i.val • x i) (fun (x: Fin p.m → G) ↦ ∑ i, i.val • x i) _
      with ω <;> try infer_instance
    all_goals try fun_prop
    . ext ω; simp [Finset.smul_sum]
    . ext ω; simp [Finset.smul_sum]; rw [Finset.sum_comm]
    simp
  . apply multiTauMinimizes_of_ident p _ _ _ h_min
    intro i; exact (hident i zero).symm
  intro j; use Equiv.refl _
  simp
  apply IdentDistrib.iprodMk _ hΩ'_prob hΩ'_prob (hindep_j j) (hindep_j zero)
  intro i
  exact (hident i j).trans (hident i zero).symm

lemma torsion_mul_eq {i j:ℤ} (x:G) (h: i ≡ j [ZMOD p.m]) : i • x = j • x := by
  rw [Int.modEq_iff_add_fac] at h
  obtain ⟨ t, rfl ⟩ := h
  simp [add_smul, mul_comm, mul_zsmul, p.htorsion]

include h_mes h_indep hident h_min in
lemma mutual_information_le_t_23 : I[Z2 : Z3 | W] ≤ p.m * (4*p.m+1) * p.η * k := by
  have hm := p.hm
  have _ : NeZero p.m := by rw [neZero_iff]; linarith
  let zero : Fin p.m := ⟨ 0, by linarith [hm]⟩
  let X' : Fin p.m × Fin p.m → Ω' → G := fun (i, j) ω ↦ Y (i-j, j) ω
  have hX'_indep : iIndepFun X' := by
    let S : Fin p.m × Fin p.m → Finset (Fin p.m × Fin p.m) := fun (i,j) ↦ {(i-j,j)}
    let φ : (q:Fin p.m × Fin p.m) → ((_: S q) → G) → G := fun q x ↦ x ⟨ (q.1-q.2,q.2), by simp [S] ⟩
    convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with i ω
    rw [Finset.pairwiseDisjoint_iff]; rintro ⟨ i,j ⟩ _ ⟨ i',j' ⟩ _ ⟨ ⟨ i₀, j₀ ⟩, hij ⟩
    simp [S] at hij; obtain ⟨ ⟨ rfl, rfl ⟩, h1, rfl ⟩ := hij; simpa using h1
  have hindep_j (j: Fin p.m) : iIndepFun (fun i ↦ X' (i, j)) := by
    let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun i ↦ {(i,j)}
    let φ : (i:Fin p.m) → ((_: S i) → G) → G := fun i x ↦ x ⟨ (i,j), by simp [S] ⟩
    convert iIndepFun.finsets_comp S _ hX'_indep (by fun_prop) φ (by fun_prop) with i ω
    rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
    simp [S] at hij; cc
  have := mutual_information_le (by fun_prop) (indep_yj h_mes h_indep zero) ?_ (by fun_prop) hX'_indep ?_
  . have k_eq : k = D[fun i ω ↦ Y (i, zero) ω ; fun x ↦ hΩ'] := by
      apply multiDist_copy; intro i; exact (hident i zero).symm
    rw [←k_eq] at this
    apply LE.le.trans _ this
    convert condMutual_comp_comp_le _ _ _ _ (fun (x: Fin p.m → G) ↦ ∑ i, i.val • x i) (fun (x: Fin p.m → G) ↦ -∑ i, i.val • x i) _
      with ω <;> try infer_instance
    all_goals try fun_prop
    . ext ω; simp [Finset.smul_sum, X']; nth_rewrite 1 [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      symm; convert Equiv.sum_comp (Equiv.subRight j) _ with i _
      simp
    . ext ω; simp [Finset.smul_sum, X',←Finset.sum_neg_distrib]; nth_rewrite 1 [Finset.sum_comm]; nth_rewrite 2 [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      symm; convert Equiv.sum_comp (Equiv.subRight j) _ with i _
      simp [←natCast_zsmul]; rw [←neg_zsmul]
      apply torsion_mul_eq (p := p)
      simp [Lean.Omega.Fin.ofNat_val_sub, Int.modEq_iff_add_fac, Int.emod_def]
      use ((↑p.m - ↑↑j + ↑↑i) / ↑p.m) - 1
      ring
    simp [X']; nth_rewrite 1 [Finset.sum_comm]; nth_rewrite 2 [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    convert Equiv.sum_comp (Equiv.subRight i) _ with j _
    simp
  . apply multiTauMinimizes_of_ident p _ _ _ h_min
    intro i; exact (hident i zero).symm
  intro j; use Equiv.subRight j
  apply IdentDistrib.iprodMk _ hΩ'_prob hΩ'_prob (hindep_j j)
  . exact iIndepFun.precomp (Equiv.injective (Equiv.subRight j)) (indep_yj h_mes h_indep zero)
  intro i
  simp [X']
  exact (hident (i-j) j).trans (hident (i-j) zero).symm

include h_mes h_indep hident h_min in
lemma mutual_information_le_t_21 : I[Z1 : Z3 | W] ≤ p.m * (4*p.m+1) * p.η * k := by
  have hm := p.hm
  have _ : NeZero p.m := by rw [neZero_iff]; linarith
  let zero : Fin p.m := ⟨ 0, by linarith [hm]⟩
  let X' : Fin p.m × Fin p.m → Ω' → G := fun (i, j) ω ↦ Y (i, j-i) ω
  have hX'_indep : iIndepFun X' := by
    let S : Fin p.m × Fin p.m → Finset (Fin p.m × Fin p.m) := fun (i,j) ↦ {(i,j-i)}
    let φ : (q:Fin p.m × Fin p.m) → ((_: S q) → G) → G := fun q x ↦ x ⟨ (q.1,q.2-q.1), by simp [S] ⟩
    convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with i ω
    rw [Finset.pairwiseDisjoint_iff]; rintro ⟨ i,j ⟩ _ ⟨ i',j' ⟩ _ ⟨ ⟨ i₀, j₀ ⟩, hij ⟩
    simp [S] at hij; obtain ⟨ ⟨ rfl, rfl ⟩, rfl, h2 ⟩ := hij; simpa using h2
  have hindep_j (j: Fin p.m) : iIndepFun (fun i ↦ X' (i, j)) := by
    let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun i ↦ {(i,j)}
    let φ : (i:Fin p.m) → ((_: S i) → G) → G := fun i x ↦ x ⟨ (i,j), by simp [S] ⟩
    convert iIndepFun.finsets_comp S _ hX'_indep (by fun_prop) φ (by fun_prop) with i ω
    rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
    simp [S] at hij; cc
  have hindep_yj (j: Fin p.m) : iIndepFun (fun i ↦ Y (i, j)) := indep_yj h_mes h_indep j
  have := mutual_information_le (by fun_prop) (hindep_yj zero) ?_ (by fun_prop) hX'_indep ?_
  . have k_eq : k = D[fun i ω ↦ Y (i, zero) ω ; fun x ↦ hΩ'] := by
      apply multiDist_copy; intro i; exact (hident i zero).symm
    rw [←k_eq,condMutualInfo_comm] at this
    apply LE.le.trans _ this
    convert condMutual_comp_comp_le _ _ _ _ (fun (x: Fin p.m → G) ↦ ∑ i, i.val • x i) (fun (x: Fin p.m → G) ↦ -∑ i, i.val • x i) _
      with ω <;> try infer_instance
    all_goals try fun_prop
    . ext ω; simp [Finset.smul_sum, X']
      apply Finset.sum_congr rfl; intro j _
      symm; convert Equiv.sum_comp (Equiv.subRight j) _ with i _
      simp
    . ext ω; simp [Finset.smul_sum, X',←Finset.sum_neg_distrib]; nth_rewrite 2 [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      symm; convert Equiv.sum_comp (Equiv.subRight j) _ with i _
      simp [←natCast_zsmul]; rw [←neg_zsmul]
      apply torsion_mul_eq (p := p)
      simp [Lean.Omega.Fin.ofNat_val_sub, Int.modEq_iff_add_fac, Int.emod_def]
      use ((↑p.m - ↑↑j + ↑↑i) / ↑p.m) - 1
      ring
    simp [X']
    apply Finset.sum_congr rfl; intro i _
    convert Equiv.sum_comp (Equiv.subRight i) _ with j _
    simp
  . apply multiTauMinimizes_of_ident p _ _ _ h_min
    intro i; exact (hident i zero).symm
  intro j; use Equiv.refl _
  simp [X']
  apply IdentDistrib.iprodMk _ hΩ'_prob hΩ'_prob (hindep_j j) (hindep_yj zero)
  intro i
  exact (hident i (j-i)).trans (hident i zero).symm

include h_mes h_indep hident in
lemma Q_ident (j j': Fin p.m) : IdentDistrib (Q j) (Q j') ℙ ℙ := by
  let f : (Fin p.m → G) → G := fun x ↦ ∑ i, x i
  convert_to IdentDistrib (f ∘ (fun ω i ↦ Y (i,j) ω)) (f ∘ (fun ω i ↦ Y (i,j') ω)) ℙ ℙ
  . ext ω; simp [f]
  . ext ω; simp [f]
  apply IdentDistrib.comp _ (by fun_prop)
  exact {
    aemeasurable_fst := by fun_prop
    aemeasurable_snd := by fun_prop
    map_eq := by
      rw [(iIndepFun_iff_map_fun_eq_pi_map (by fun_prop)).mp _, (iIndepFun_iff_map_fun_eq_pi_map (by fun_prop)).mp _]
      . congr 1; ext1 i
        exact ((hident i j).trans (hident i j').symm).map_eq
      . exact indep_yj h_mes h_indep j'
      exact indep_yj h_mes h_indep j
      }

include h_mes in
omit hΩ'_prob in
lemma Q_mes (j: Fin p.m) : Measurable (-(Q j)) := by
  apply Measurable.neg; fun_prop

include h_mes h_indep hident in
lemma Q_dist (j j': Fin p.m) : d[Q j # -(Q j')] ≤ 2 * k := by
  have : IdentDistrib (Q j) (Q j') ℙ ℙ := Q_ident _ h_mes h_indep hident _ _
  have hQj_mes : Measurable (-(Q j')) := Q_mes h_mes _
  calc
    _ = d[Q j' # -(Q j')] := IdentDistrib.rdist_congr_left (by fun_prop) this
    _ ≤ _ := by
      convert multidist_ruzsa_IV p.hm (fun i ω ↦ Y (i, j') ω) _ (by simp; fun_prop) (inferInstance) using 2
      . apply multiDist_copy; intro i; convert (hident i j').symm
      exact indep_yj h_mes h_indep j'

include h_mes h_indep hident in
lemma Q_ent (j: Fin p.m) : H[Q j] = k + (↑p.m)⁻¹ * ∑ i, H[X i] := by
  rw [Q_eq, inv_mul_eq_div]
  have h1 := multiDist_indep hΩ' (fun i:Fin p.m ↦ h_mes i j) ?_
  . have h2 : D[fun i ↦ Y (i, j) ; fun x ↦ hΩ'] = k := by
      apply multiDist_copy; intros; solve_by_elim
    have h3 (i:Fin p.m) : H[Y (i, j)] = H[X i] := by
      apply IdentDistrib.entropy_congr; solve_by_elim
    simp [h2, h3] at h1
    linarith
  exact indep_yj h_mes h_indep j

include h_mes h_indep in
omit hΩ'_prob in
lemma Q_indep {j j': Fin p.m} (h:j ≠ j') : IndepFun (Q j) (-Q j') ℙ := by
  let T : Finset (Fin p.m × Fin p.m) := {q|q.2=j}
  let T' : Finset (Fin p.m × Fin p.m) := {q|q.2=j'}
  let φ : (T → G) → G := fun f ↦ ∑ i, f ⟨ (i,j), by simp [T] ⟩
  let φ' : (T' → G) → G := fun f ↦ -∑ i, f ⟨ (i,j'), by simp [T'] ⟩
  convert iIndepFun.finsets_comp' _ h_indep (by fun_prop) (show Measurable φ by fun_prop) (show Measurable φ' by fun_prop) with ω ω <;> try simp [φ,φ']
  rw [Finset.disjoint_left]; rintro ⟨ _, _ ⟩ h h'
  simp [T,T'] at h h'; order

include h_mes h_indep hident in
/-- We have $\bbH[W] \leq (2m-1)k + \frac1m \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_W_le : H[W] ≤ (2*p.m - 1) * k + (p.m:ℝ)⁻¹ * ∑ i, H[X i] := by
  have hm := p.hm
  let zero : Fin p.m := ⟨ 0, by linarith [hm]⟩
  calc
    _ = H[∑ i, Q i] := by rw [Finset.sum_comm]
    _ = H[Q zero + ∑ i ∈ .Ioi zero, Q i] := by
      congr; rw [add_comm]
      convert (Finset.sum_erase_add _ _ (show zero ∈ .univ by simp)).symm using 3
      ext ⟨ i, hi ⟩; simp [zero]; omega
    _ ≤ H[Q zero] + ∑ i ∈ .Ioi zero, (H[Q zero + Q i] - H[Q zero]) := by
      rw [←sub_le_iff_le_add']
      convert kvm_ineq_I (s := .Ioi zero) _ _ _ <;> try infer_instance
      . simp
      . fun_prop
      let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun j ↦ {p|p.2=j}
      let φ : (j:Fin p.m) → ((_: S j) → G) → G := fun j x ↦ ∑ i, x ⟨ (i,j), by simp [S] ⟩
      convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with i ω
      . simp [φ]
      rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
      simp [S] at hij; cc
    _ ≤ k + (p.m:ℝ)⁻¹ * ∑ i, H[X i] + ∑ i ∈ .Ioi zero, 2 * k := by
      gcongr with j hj
      . exact le_of_eq (Q_ent _ h_mes h_indep hident _)
      simp at hj
      have : IdentDistrib (Q zero) (Q j) ℙ ℙ := Q_ident _ h_mes h_indep hident _ _
      have hQj_mes : Measurable (-(Q j)) := Q_mes h_mes _
      calc
        _ = d[Q zero # -(Q j)] := by
          rw [ProbabilityTheory.IndepFun.rdist_eq _ (by fun_prop) hQj_mes, entropy_neg (by fun_prop), ←IdentDistrib.entropy_congr this, sub_neg_eq_add]
          . linarith
          exact Q_indep h_mes h_indep (by order)
        _ ≤ _ := Q_dist _ h_mes h_indep hident _ _
    _ = _ := by
      have : (p.m-1:ℕ) = (p.m:ℝ)-(1:ℝ) := by norm_cast; apply (Int.subNatNat_of_le _).symm; omega
      simp [zero, this]; ring

set_option linter.unusedSectionVars false in
lemma Z2_eq : Z2 = ∑ j ∈ Finset.univ.erase ⟨ 0, by linarith [p.hm]⟩, j.val • Q j := calc
  _ = ∑ j, j.val • Q j := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; simp [←Finset.smul_sum]
  _ = ∑ j ∈ Finset.univ.erase ⟨ 0, by linarith [p.hm]⟩, j.val • Q j  := by symm; apply Finset.sum_erase; simp

include h_mes h_indep hident in
/-- We have $\bbH[Z_2] \leq (8m^2-16m+1) k + \frac{1}{m} \sum_{i=1}^m \bbH[X_i]$. -/
lemma entropy_of_Z_two_le : H[Z2] ≤ (8 * p.m^2 - 16 * p.m + 1) * k + (p.m:ℝ)⁻¹ * ∑ i, H[X i] := by
  have hm := p.hm
  let zero : Fin p.m := ⟨ 0, by linarith [hm]⟩
  let one : Fin p.m := ⟨ 1, by linarith [hm]⟩
  let Y' : Fin p.m → Ω' → G := fun i ω ↦ i.val • Q i ω
  have : Y' one = Q one := by ext; simp [one, Y']
  calc
    _ = H[ Q one + ∑ i ∈ .Ioi one, i.val • (Q i)] := by
      congr
      calc
        _ = ∑ j ∈ Finset.univ.erase zero, j.val • Q j  := Z2_eq
        _ = _ := by
          symm; rw [add_comm, ←this]
          convert Finset.sum_erase_add _ _ _ using 3 <;> try infer_instance
          . ext ⟨ _, _ ⟩; simp [zero, one]; omega
          simp [one, zero]
    _ ≤ H[Q one] + ∑ i ∈ .Ioi one, (H[Q one + i.val • (Q i)] - H[Q one]) := by
      rw [←sub_le_iff_le_add']
      simp_rw [←this]
      convert kvm_ineq_I (s := .Ioi one) _ _ _ using 1 <;> try infer_instance
      . simp
      . fun_prop
      let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun j ↦ {p|p.2=j}
      let φ : (j:Fin p.m) → ((_: S j) → G) → G := fun j x ↦ j.val • ∑ i, x ⟨ (i,j), by simp [S] ⟩
      convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with i ω
      . simp [φ, Y']
      rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
      simp [S] at hij; cc
    _ ≤ H[Q one] + ∑ i ∈ .Ioi one, 4 * p.m * (2 * k) := by
      gcongr with i hi
      have hQi_mes : Measurable (-(Q i)) := Q_mes h_mes _
      calc
        _ = H[Q one - (i.val:ℤ) • -(Q i)] - H[Q one]:= by simp
        _ ≤ 4 * |(i.val:ℤ)| * d[Q one # -(Q i)] := by
          convert ent_sub_zsmul_sub_ent_le _ _ _ <;> try infer_instance
          all_goals try fun_prop
          simp at hi; exact Q_indep h_mes h_indep (by order)
        _ ≤ _ := by
          gcongr
          . exact rdist_nonneg (by fun_prop) (by fun_prop)
          . simp
          exact Q_dist _ h_mes h_indep hident _ _
    _ ≤ k + (p.m:ℝ)⁻¹ * ∑ i, H[X i] + ∑ i ∈ .Ioi one, 4 * p.m * (2 * k) := by
      gcongr; exact le_of_eq (Q_ent _ h_mes h_indep hident _)
    _ = _ := by
      have : (p.m-1-1:ℕ) = (p.m:ℝ)-(1:ℝ)-(1:ℝ) := by norm_cast; rw [Int.subNatNat_of_le (by omega)]; omega
      simp [one, this]; ring

include h_mes h_indep hident in
/-- We have $\bbI[W : Z_2] \leq 2(m-1) k$. -/
lemma mutual_of_W_Z_two_le : I[W : Z2] ≤ 2 * (p.m-1) * k := by
  rw [mutualInfo_eq_entropy_sub_condEntropy (by fun_prop) (by fun_prop)]
  have hm := p.hm
  let zero : Fin p.m := ⟨ 0, by linarith [hm]⟩
  have h1 := entropy_of_W_le _ h_mes h_indep hident
  have h2 : H[W | Z2] ≥ H[Q zero] := calc
    _ ≥ H[W | fun ω (i : Finset.univ.erase zero) ↦ Q (i.val) ω] := by
      let f : (Finset.univ.erase zero → G) → G := fun x ↦ ∑ j, j.val.val • (x j)
      convert condEntropy_comp_ge _ _ _ f <;> try infer_instance
      . ext ω; simp only [Z2_eq, f]
        simp only [Finset.sum_apply, Pi.smul_apply, Finset.mem_univ, Function.comp_apply]
        convert Finset.sum_subtype _ _ _
        simp [zero]
      all_goals fun_prop
    _ = H[Q zero | fun ω (i : Finset.univ.erase zero) ↦ Q (i.val) ω] := by
      let f : (Finset.univ.erase zero → G) → G → G := fun x y ↦ y + ∑ j, x j
      convert condEntropy_of_injective _ _ _ f _ with ω <;> try infer_instance
      all_goals try fun_prop
      . simp [f]; rw [Finset.sum_comm]
        symm; convert Finset.add_sum_erase (a := zero) _ _ _
        . rfl
        . convert Finset.sum_attach _ _; rfl
        simp
      intro _ _ _ h; simpa [f] using h
    _ = _ := by
      apply IndepFun.condEntropy_eq_entropy _ (by fun_prop) (by fun_prop)
      let T : Finset (Fin p.m × Fin p.m) := {q|q.2=zero}
      let T' : Finset (Fin p.m × Fin p.m) := Tᶜ
      let φ : (T → G) → G := fun f ↦ ∑ i, f ⟨ (i,zero), by simp [T] ⟩
      let φ' : (T' → G) → (Finset.univ.erase zero → G) := fun f j ↦ ∑ i, f ⟨ (i,j), by obtain ⟨ j, hj ⟩ := j;  simpa [T,T'] using hj⟩
      convert iIndepFun.finsets_comp' _ h_indep (by fun_prop) (show Measurable φ by fun_prop) (show Measurable φ' by fun_prop) with ω ω <;> try simp [φ,φ']
      simp [T', disjoint_compl_right]
  have h3 := Q_ent _ h_mes h_indep hident zero
  have h4 : (2 * ↑p.m - 1) * k - k = 2 * (↑p.m - 1) * k := by ring
  linarith

include h_mes h_indep hident hΩ_prob hX_mes in
/-- We have $\sum_{i=1}^m d[X_i;Z_2|W] \leq 8(m^3-m^2) k$. -/
lemma sum_of_conditional_distance_le : ∑ i, d[ X i # Z2 | W] ≤ 4 * (p.m^3 - p.m^2)*k := by
  have hm := p.hm
  let zero : Fin p.m := ⟨ 0, by linarith [hm]⟩
  let one : Fin p.m := ⟨ 1, by linarith [hm]⟩
  have hm_2 : (p.m:ℝ) ≥ 2 := by norm_cast
  have hm_pos : (p.m:ℝ) > 0 := by linarith
  have hm_pos' : 2*(p.m:ℝ)-1 > 0 := by linarith
  have hk : k ≥ 0 := multiDist_nonneg _ hΩ_prob _ hX_mes
  calc
    _ ≤ ∑ i, (d[ X i # X i] + (H[Z2] - H[X i])/ 2 + (p.m-1) * k) := by
      apply Finset.sum_le_sum; intro i _; calc
        _ ≤ d[X i # Z2] + I[W:Z2] / 2 := by
          rw [mutualInfo_comm]
          convert condRuzsaDist_le' _ _ _ _ _ <;> try infer_instance
          all_goals fun_prop
        _ ≤ (d[X i # X i] + (H[Z2] - H[X i]) / 2) + (2*(p.m-1) * k)/2 := by
          gcongr
          . rw [div_eq_inv_mul]
            let i₀ : Fin p.m × Fin p.m := (i, zero)
            let i₁ : Fin p.m × Fin p.m := (i, one)
            let Y' : Fin p.m × Fin p.m → Ω' → G := fun q ↦ if q = i₀ then Y q else q.2.val • Y q
            have h_mes_Y' (q: Fin p.m × Fin p.m) : Measurable (Y' q) := by
              by_cases h : q = i₀ <;> simp [Y', h] <;> fun_prop
            let s : Finset (Fin p.m × Fin p.m) := Finset.erase {q | q.2 ≠ zero} i₁
            have hs₀: i₀ ∉ s := by simp [s, i₀]
            have hs₁: i₁ ∉ s := by simp [s, i₁]
            have h01: i₀ ≠ i₁ := by simp [i₀, i₁,zero,one]
            have : Z2 = Y' i₁ + ∑ p ∈ s, Y' p := by
              simp_rw [Z2_eq, Finset.smul_sum]; rw [Finset.sum_comm]
              calc
                _ = ∑ q ∈ Finset.univ ×ˢ (Finset.univ.erase zero), q.2.val • Y q := by
                  symm; convert Finset.sum_product _ _ _
                _ = ∑ q ∈ Finset.univ ×ˢ (Finset.univ.erase zero), Y' q := by
                  apply Finset.sum_congr rfl; intro ⟨ i, j ⟩ hq
                  simp [Y',i₀] at hq ⊢; tauto
                _ = _ := by
                  symm; convert Finset.add_sum_erase _ _ _
                  . ext ⟨ i,j ⟩; simp
                  simp [i₁, zero, one]
            rw [this]
            have hident₀ : IdentDistrib (Y' i₀) (X i) ℙ ℙ := by
              convert hident i zero using 1
              simp [Y', i₀]
            have hident₁ : IdentDistrib (Y' i₁) (X i) ℙ ℙ := by
              convert hident i one using 1
              simp [Y', i₁,i₀,one,zero]
            rw [←IdentDistrib.entropy_congr hident₁, ←IdentDistrib.rdist_congr hident₀ hident₁, ←IdentDistrib.rdist_congr hident₀ (IdentDistrib.refl (by fun_prop))]
            convert kvm_ineq_III hs₀ hs₁ h01 Y' h_mes_Y' _
            let S : Fin p.m × Fin p.m → Finset (Fin p.m × Fin p.m) := fun q ↦ {q}
            let φ : (q:Fin p.m × Fin p.m) → ((_: S q) → G) → G :=
              fun q x ↦ if q = i₀ then x ⟨ q, by simp [S] ⟩ else q.2.val • x ⟨ q, by simp [S] ⟩
            convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with q ω
            . by_cases h : q = i₀ <;> simp [φ,Y',h]
            rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
            simp [S] at hij; cc
          exact mutual_of_W_Z_two_le _ h_mes h_indep hident
        _ = _ := by ring
    _ = ∑ i, d[ X i # X i] + p.m * H[Z2] / 2 - (∑ i, H[X i]) / 2 + p.m * (p.m -1) * k := by
      simp [Finset.sum_add_distrib, ←Finset.sum_div, Finset.sum_sub_distrib, sub_div]; ring
    _ ≤ ∑ i, d[ X i # X i] + p.m * ((8 * p.m^2 - 16 * p.m + 1) * k + (p.m:ℝ)⁻¹ * ∑ i, H[X i])/2 - (∑ i, H[X i]) / 2  + p.m * (p.m -1) * k := by
      gcongr; exact entropy_of_Z_two_le _ h_mes h_indep hident
    _ = ∑ i, d[ X i # X i] + p.m * (8 * p.m^2 - 16 * p.m + 1) * k / 2 + p.m * (p.m -1) * k:= by
      field_simp; ring
    _ ≤ 2*p.m*k + p.m * (8 * p.m^2 - 16 * p.m + 1) * k / 2 + p.m * (p.m -1) * k := by
      gcongr
      exact multidist_ruzsa_II p.hm _ hΩ_prob _ hX_mes (inferInstance)
    _ = 4 * (p.m^3 - p.m^2) * k - 3 * p.m * (2*p.m - 1) * k /2 := by ring
    _ ≤ _ := by
      simp; positivity

lemma pigeonhole {G:Type*} [MeasureSpace G] [IsProbabilityMeasure (ℙ:Measure G)] [Fintype G]
  [MeasurableSingletonClass G] (f: G → ℝ) : ∃ x, f x ≤ ∫ (z : G), f z ∧ ℙ {x} ≠ 0 := by
  set I := ∫ (z : G), f z with hI
  simp [integral_fintype] at hI
  by_contra!
  have hI': ∑ x, (ℙ:Measure G).real {x} * f x > ∑ x, (ℙ:Measure G).real {x} * I := by
    apply Finset.sum_lt_sum
    . intro i _
      by_cases h : I ≤ f i
      . gcongr
      specialize this i (by order)
      rw [←measureReal_eq_zero_iff] at this
      simp [this]
    have : ∑ x, (ℙ:Measure G).real {x} = 1 := by simp
    replace : ∃ x, (ℙ:Measure G).real {x} ≠ 0 := by contrapose! this; simp [this]
    obtain ⟨ x, hx ⟩ := this
    use x, by simp
    gcongr; contrapose! hx
    specialize this x hx; simpa [measureReal_eq_zero_iff] using this
  simp [←Finset.sum_mul, sum_measureReal_singleton] at hI'
  order

/-- Let $G$ be an abelian group, let $(T_1,T_2,T_3)$ be a $G^3$-valued random variable such that $T_1+T_2+T_3=0$ holds identically, and write
  \[
    \delta := \bbI[T_1 : T_2] + \bbI[T_1 : T_3] + \bbI[T_2 : T_3].
  \]
  Let $Y_1,\dots,Y_n$ be some further $G$-valued random variables and let $\alpha>0$ be a constant.
  Then there exists a random variable $U$ such that
$$  d[U;U] + \alpha \sum_{i=1}^n d[Y_i;U] \leq \Bigl(2 + \frac{\alpha n}{2} \Bigr) \delta + \alpha \sum_{i=1}^n d[Y_i;T_2].
$$
-/
lemma dist_of_U_add_le {G: Type*} [MeasurableFinGroup G] {Ω : Type u} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ:Measure Ω)] {T₁ T₂ T₃ : Ω → G}
  (hsum: T₁ + T₂ + T₃ = 0) (hmes₁: Measurable T₁) (hmes₂: Measurable T₂) (hmes₃: Measurable T₃)
  {n:ℕ} {Ω': Fin n → Type*} (hΩ': ∀ i, MeasureSpace (Ω' i)) [∀ i, IsProbabilityMeasure (hΩ' i).volume]
  {Y: ∀ i, (Ω' i) → G} (hY: ∀ i, Measurable (Y i)) {α:ℝ} (hα: α > 0) :
  ∃ (Ω'':Type u) (hΩ'': MeasureSpace Ω'') (U: Ω'' → G), IsProbabilityMeasure hΩ''.volume ∧ d[U # U] + α * ∑ i, d[Y i # U] ≤ (2 + α * n / 2) * (I[T₁ : T₂] + I[T₁ : T₃] + I[T₂ : T₃]) + α * ∑ i, d[Y i # T₂] := by
  let δ := I[T₁ : T₂] + I[T₁ : T₃] + I[T₂ : T₃]
  have h1 := ent_bsg (μ := ℙ) hmes₁ hmes₂
  have h₁₂ : I[T₁ : T₂] = H[T₁] + H[T₂] - H[ ⟨ T₁, T₂ ⟩ ] := mutualInfo_def _ _ _
  have h₁₃ : I[T₁ : T₃] = H[T₁] + H[T₃] - H[ ⟨ T₁, T₃ ⟩ ] := mutualInfo_def _ _ _
  have h₂₃ : I[T₂ : T₃] = H[T₂] + H[T₃] - H[ ⟨ T₂, T₃ ⟩ ] := mutualInfo_def _ _ _
  have h₃_neg : H[T₁+T₂] = H[T₃] := by rw [←entropy_neg]; congr; rwa [←add_eq_zero_iff_neg_eq]; fun_prop
  have h₁₃_eq : H[ ⟨ T₁, T₃ ⟩ ] = H[ ⟨ T₁, T₂ ⟩ ] := by
    rw [←entropy_add_right', ←entropy_neg_right] <;> try fun_prop
    congr!; rw [←add_eq_zero_iff_neg_eq, ←hsum]; abel
  have h₂₃_eq : H[ ⟨ T₁, T₃ ⟩ ] = H[ ⟨ T₂, T₃ ⟩ ] := by
    rw [←entropy_add_left', ←entropy_neg_left] <;> try fun_prop
    congr!; rw [←add_eq_zero_iff_neg_eq, ←hsum]; abel
  let _hG : MeasureSpace G := ⟨Measure.map (T₁ + T₂) ℙ⟩
  let _ : IsProbabilityMeasure (ℙ: Measure G) := isProbabilityMeasure_map (by fun_prop)
  change ∫ (x : G), (fun z ↦ d[T₁ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]]) x ≤ 3 * I[T₁ : T₂] + 2 * H[T₁ + T₂] - H[T₁] - H[T₂] at h1
  replace h1 : ∫ (z : G), 2 * d[T₁ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] ≤ 2 * δ := by rw [integral_const_mul_of_integrable]; linarith; apply MeasureTheory.Integrable.of_finite
  replace h1 : ∫ (z : G), d[T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] ≤ 2 * δ := by
    apply LE.le.trans _ h1
    apply MeasureTheory.integral_mono <;> try apply MeasureTheory.Integrable.of_finite
    intro z; simp
    by_cases h : ℙ ( (T₁+T₂) ⁻¹' {z} ) = 0
    . simp [cond_eq_zero_of_meas_eq_zero h, rdist_def]
    have : IsProbabilityMeasure ℙ[|(T₁ + T₂) ⁻¹' {z}] := cond_isProbabilityMeasure h
    calc
      _ ≤ d[T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₁ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] + d[T₁ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] := rdist_triangle (by fun_prop) (by fun_prop) (by fun_prop)
      _ ≤ d[T₁ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] + d[T₁ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₂ ; ℙ[|(T₁+ T₂) ⁻¹' {z}]] := by rw [rdist_symm]
      _ = _ := by ring
  have h2 (i:Fin n): ∫ (z : G), d[Y i ; ℙ # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] ≤ d[Y i # T₂] + δ/2 := calc
    _ = d[Y i # T₂ | T₃] := by
      rw [condRuzsaDist'_eq_sum', integral_fintype] <;> try fun_prop
      . classical
        trans ∑ x ∈ -Finset.univ, (ℙ:Measure G).real {x} • d[Y i ; ℙ # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {x}]]
        . simp
        rw [Finset.sum_neg_index]
        apply Finset.sum_congr rfl; intro x
        have : (T₁ + T₂) ⁻¹' {-x} = T₃ ⁻¹' {x} := by
          rw [add_eq_zero_iff_eq_neg] at hsum; rw [hsum]
          ext ω; simp
        simp [_hG]; rw [map_measureReal_apply, this]
        . fun_prop
        measurability
      apply MeasureTheory.Integrable.of_finite
    _ ≤ d[Y i # T₂] + I[T₂ : T₃]/2 := by
      convert condRuzsaDist_le' _ _ _ _ _ <;> try infer_instance
      all_goals fun_prop
    _ ≤ d[Y i # T₂] + δ / 2 := by
      gcongr
      have : I[T₁ : T₂] ≥ 0 := by apply mutualInfo_nonneg <;> try fun_prop
      have : I[T₁ : T₃] ≥ 0 := by apply mutualInfo_nonneg <;> try fun_prop
      linarith
  set F: G → ℝ := fun z ↦ d[T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] + α * ∑ i, d[Y i ; ℙ # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]]
  have h3 : ∫ (z : G), F z ≤ 2 * δ + α * ∑ i, d[Y i # T₂] + α * n * δ / 2:= calc
    _ = ∫ (z : G), d[T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}] # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] ∂ℙ + α * ∑ i, ∫ (z : G), d[Y i ; ℙ # T₂ ; ℙ[|(T₁ + T₂) ⁻¹' {z}]] := by
      rw [integral_add, integral_const_mul,integral_finset_sum] <;> try intros
      all_goals apply MeasureTheory.Integrable.of_finite
    _ ≤ _ := by
      rw [add_assoc]; gcongr; calc
        _ ≤ α * ∑ i, (d[Y i # T₂] + δ/2) := by
          gcongr with i; exact h2 i
        _ = _ := by
          simp [Finset.sum_add_distrib]; ring
  obtain ⟨ z, hz, hpos ⟩ := pigeonhole F
  replace h3 := hz.trans h3
  use Ω, ⟨ ℙ[|(T₁ + T₂) ⁻¹' {z}] ⟩, T₂
  constructor
  . apply cond_isProbabilityMeasure
    convert hpos
    simp [_hG]; rw [MeasureTheory.Measure.map_apply (by fun_prop) (by measurability)]
  convert h3 using 1
  ring


/-- We have $k = 0$. -/
lemma k_eq_zero : k = 0 := sorry

end AnalyzeMinimizer

universe u
/-- Suppose that $G$ is a finite abelian group of torsion $m$. Suppose that $X$ is a $G$-valued random variable. Then there exists a subgroup $H \leq G$ such that \[ d[X;U_H] \leq 64 m^3 d[X;X].\] -/
lemma dist_of_X_U_H_le {G : Type u} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
  [MeasurableSingletonClass G] {m:ℕ} (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) {Ω : Type u} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ:Measure Ω)] {X: Ω → G} (hX: Measurable X) : ∃ H : AddSubgroup G, ∃ Ω' : Type u, ∃ mΩ : MeasureSpace Ω', IsProbabilityMeasure mΩ.volume ∧ ∃ U : Ω' → G,
    IsUniform H U ∧ Measurable U ∧ d[X # U] ≤ 64 * m^3 * d[X # X] := by
    let _ : MeasurableFinGroup G := {
    }
    let p : multiRefPackage G Ω := {
      m := m
      hm := hm
      htorsion := htorsion
      hprob := inferInstance
      X₀ := X
      hmeas := hX
      η := 1 / (32 * m^3)
      hη := by positivity
      hη' := by rw [one_div, inv_le_one₀ (by positivity)]; norm_cast; linarith [Nat.pow_le_pow_left hm 3]
    }
    obtain ⟨ Ω', mΩ', X', hX'_mes, hΩ'_prob, htau_min ⟩ := multiTau_min_exists p
    have hdist : D[X'; mΩ'] = 0 := by
      apply k_eq_zero
    have hclose : ∃ i, d[X' i # p.X₀] ≤ (2/p.η) * d[p.X₀ # p.X₀] := by
      by_contra!
      replace : ∑ i:Fin p.m, 2 / p.η * d[p.X₀ # p.X₀] < ∑ i, d[X' i # p.X₀] := by
        apply Finset.sum_lt_sum_of_nonempty
        . use ⟨ 0, by linarith ⟩; simp
        simp [this]
      simp at this
      have h' := multiTau_min_sum_le p _ mΩ' hΩ'_prob _ hX'_mes htau_min
      have h'' : ↑p.m * (2 / p.η * d[p.X₀ # p.X₀]) =  2 * ↑p.m * p.η⁻¹ * d[p.X₀ # p.X₀] := by
        field_simp; ring
      order
    obtain ⟨ i, hclose ⟩ := hclose
    obtain ⟨ H, U, hU_mes, hU_unif, hdist ⟩ := multidist_eq_zero hm mΩ' hΩ'_prob _ hdist hX'_mes (inferInstance) i
    replace hclose : d[p.X₀ # U] ≤ (2/p.η) * d[p.X₀ # p.X₀] := calc
      _ ≤ d[p.X₀ # X' i] + d[X' i # U] := rdist_triangle hX (by fun_prop) (by fun_prop)
      _ = d[X' i # p.X₀] := by simp [hdist]; exact rdist_symm
      _ ≤ _ := hclose
    refine ⟨ H, Ω' i, mΩ' i, hΩ'_prob i, U, hU_unif, hU_mes, ?_ ⟩
    convert hclose using 2
    have : m > (0:ℝ) := by norm_cast; linarith
    simp [p]; field_simp; ring

open Real

/-- A uniform distribution on a set with doubling constant `K` has self Rusza distance
at most `log K`. -/
theorem rdist_le_of_isUniform_of_card_add_le' {G : Type*} [AddCommGroup G] {A : Set G}
    {K : ℝ} [Countable G] [A_fin : Finite A] [MeasurableSpace G]
    [MeasurableSingletonClass G]
    (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A)
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U₀ : Ω → G}
    (U₀unif : IsUniform A U₀) (U₀meas : Measurable U₀) : d[U₀ # -U₀] ≤ log K := by
  obtain ⟨A_pos, AA_pos, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' h₀A hA
  rcases independent_copies_two U₀meas U₀meas with ⟨Ω, mΩ, U, U', hP, hU, hU', UU'_indep, idU, idU'⟩
  have Uunif : IsUniform A U := U₀unif.of_identDistrib idU.symm .of_discrete
  have U'unif : IsUniform A U' := U₀unif.of_identDistrib idU'.symm .of_discrete
  have IU : d[U # -U'] ≤ log K := by
    have I : H[U - (-U')] ≤ log (Nat.card (A + A)) := by
      simp only [sub_neg_eq_add]
      apply entropy_le_log_card_of_mem_finite (Set.Finite.add A_fin A_fin) (hU.add hU')
      filter_upwards [Uunif.ae_mem, U'unif.ae_mem] with ω h1 h2
      exact Set.add_mem_add h1 h2
    have J : log (Nat.card (A + A)) ≤ log K + log (Nat.card A) := by
      apply (log_le_log AA_pos hA).trans (le_of_eq _)
      rw [log_mul K_pos.ne' A_pos.ne']
    have A_fin_neg : Finite (-A: Set G) := Set.Finite.neg A_fin
    replace UU'_indep : IndepFun U (-U') ℙ := by exact ProbabilityTheory.IndepFun.neg_right UU'_indep
    replace U'unif : IsUniform (-A) (-U') := by
      let A' := A.toFinite.toFinset
      have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
      rw [←hAA'] at U'unif
      classical
      convert IsUniform.comp U'unif neg_injective
      ext x; simp [hAA']
    rw [UU'_indep.rdist_eq hU hU'.neg, Uunif.entropy_eq' A_fin hU, U'unif.entropy_eq' A_fin_neg hU'.neg]
    have : log (Nat.card (-A: Set G)) = log (Nat.card A) := by
      congr 2; simp
    linarith
  replace idU' : IdentDistrib (-U') (-U₀) ℙ ℙ := by
    convert ProbabilityTheory.IdentDistrib.comp idU' (u := fun x ↦ -x) (by fun_prop)
  rwa [idU.rdist_congr idU'] at IU

/-- Suppose that $G$ is a finite abelian group of torsion $m$. If $A \subset G$ is non-empty and
  $|A+A| \leq K|A|$, then $A$ can be covered by at most $K ^
  {(64m^3+2)/2}|A|^{1/2}/|H|^{1/2}$ translates of a subspace $H$ of $G$ with
 $|H|/|A| \in [K^{-64m^3}, K^{64m^3}]$
     -/
lemma torsion_PFR_conjecture_aux {G : Type*} [AddCommGroup G] [Fintype G] {m:ℕ} (hm: m ≥ 2)
    (htorsion: ∀ x:G, m • x = 0) {A : Set G} [A_fin: Finite A] {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (128 * m^3 + 1) * Nat.card A ^ (1/2:ℝ) * Nat.card H ^ (-1/2 : ℝ )
      ∧ Nat.card H ≤ K ^ (256 * m^3) * Nat.card A
      ∧ Nat.card A ≤ K ^ (256 * m^3) * Nat.card H ∧ A ⊆ c + H := by
  let _mG : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := ⟨λ _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' h₀A hA
  let A' := A.toFinite.toFinset
  have h₀A' : Finset.Nonempty A' := by simpa [Finset.Nonempty, A'] using h₀A
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' h₀A' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -, -⟩
  rw [hAA'] at UAunif
  have : d[UA # -UA] ≤ log K := rdist_le_of_isUniform_of_card_add_le' h₀A hA UAunif UAmeas
  replace : d[UA # UA] ≤ 2 * log K := calc
    _ ≤ d[UA # -UA] + d[-UA # UA] := rdist_triangle UAmeas UAmeas.neg UAmeas
    _ ≤ log K + log K := by gcongr; rwa [rdist_symm]
    _ = _ := by ring
  obtain ⟨ H, Ω₁, mΩ₁, _, UH, UHunif, UHmeas, huH ⟩ := dist_of_X_U_H_le hm htorsion UAmeas
  have H_fin : (H : Set G).Finite := (H : Set G).toFinite
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm .of_discrete
  have VA'unif := VAunif
  rw [← hAA'] at VA'unif
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm .of_discrete
  let H' := (H : Set G).toFinite.toFinset
  have hHH' : H' = (H : Set G) := (toFinite (H : Set G)).coe_toFinset
  have VH'unif := VHunif
  rw [← hHH'] at VH'unif

  have : d[VA # VH] ≤ 64 * m^3 * (2*log K) := by rw [idVA.rdist_congr idVH]; apply huH.trans; gcongr
  have H_pos : (0 : ℝ) < Nat.card H := by
    have : 0 < Nat.card H := Nat.card_pos
    positivity
  have VA_ent : H[VA] = log (Nat.card A) := VAunif.entropy_eq' A_fin VAmeas
  have VH_ent : H[VH] = log (Nat.card H) := VHunif.entropy_eq' H_fin VHmeas
  have Icard : |log (Nat.card A) - log (Nat.card H)| ≤ 256 * m^3 * log K := by
    rw [← VA_ent, ← VH_ent]
    apply (diff_ent_le_rdist VAmeas VHmeas).trans
    linarith
  have IAH : Nat.card A ≤ K ^ (256 * m^3) * Nat.card H := by
    have : log (Nat.card A) ≤ log K * (256 * m^3) + log (Nat.card H) := by
      linarith [(le_abs_self _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log A_pos).symm
    · rw [exp_add, exp_log H_pos, ← rpow_def_of_pos K_pos, ←Real.rpow_natCast]
      norm_cast
  have IHA : Nat.card H ≤ K ^ (256 * m^3) * Nat.card A := by
    have : log (Nat.card H) ≤ log K * (256 * m^3) + log (Nat.card A) := by
      linarith [(neg_le_abs _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log H_pos).symm
    · rw [exp_add, exp_log A_pos, ← rpow_def_of_pos K_pos, ←Real.rpow_natCast]
      norm_cast
  -- entropic PFR shows that the entropy of `VA - VH` is small
  have I : log K * (-128*m^3) + log (Nat.card A) * (-1/2) + log (Nat.card H) * (-1/2)
      ≤ - H[VA - VH] := by
    rw [Vindep.rdist_eq VAmeas VHmeas] at this
    linarith
  -- therefore, there exists a point `x₀` which is attained by `VA - VH` with a large probability
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- H[VA - VH]) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _ ((VAmeas.sub VHmeas).comp measurable_id')
  -- massage the previous inequality to get that `A ∩ (H + {x₀})` is large
  have J : K ^ (-128*m^3 : ℝ) * Nat.card A ^ (1/2:ℝ) * Nat.card H ^ (1/2 : ℝ) ≤
      Nat.card (A ∩ (H + {x₀}) : Set G) := by
    rw [VA'unif.measureReal_preimage_sub VAmeas VH'unif VHmeas Vindep] at h₀
    have := (Real.exp_monotone I).trans h₀
    have hAA'_card : Nat.card A' = Nat.card A := congrArg Nat.card (congrArg Subtype hAA')
    have hHH'_card : Nat.card H' = Nat.card H := congrArg Nat.card (congrArg Subtype hHH')
    rw [hAA'_card, hHH'_card, le_div_iff₀] at this
    convert this using 1
    · rw [exp_add, exp_add, ← rpow_def_of_pos K_pos, ← rpow_def_of_pos A_pos,
        ← rpow_def_of_pos H_pos]
      rpow_ring
      norm_num
    · rw [hAA', hHH']
    positivity

  have Hne : (A ∩ (H + {x₀} : Set G)).Nonempty := by
    by_contra h'
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    simp only [Nat.card_eq_fintype_card, Nat.card_of_isEmpty, CharP.cast_eq_zero, lt_self_iff_false,
      not_nonempty_iff_eq_empty.1 h'] at this
  /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  have Z3 :
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ) ≤ (K ^ (128*m^3+1 : ℝ) * Nat.card A ^ (1/2 : ℝ) *
        Nat.card H ^ (-1/2 : ℝ)) * Nat.card ↑(A ∩ (↑H + {x₀})) := by
    calc
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ)
      _ ≤ Nat.card (A + A) := by
        gcongr; exact Nat.card_mono (toFinite _) <| add_subset_add_left inter_subset_left
      _ ≤ K * Nat.card A := hA
      _ = (K ^ (128*m^3+1 : ℝ) * Nat.card A ^ (1/2 : ℝ) * Nat.card H ^ (-1/2 : ℝ)) *
          (K ^ (-128*m^3 : ℝ) * Nat.card A ^ (1/2 : ℝ) * Nat.card H ^ (1/2 : ℝ)) := by
        rpow_ring; norm_num
      _ ≤ (K ^ (128*m^3+1 : ℝ) * Nat.card A ^ (1/2 : ℝ) * Nat.card H ^ (-1/2 : ℝ)) *
        Nat.card ↑(A ∩ (↑H + {x₀})) := by gcongr
  obtain ⟨u, huA, hucard, hAu, -⟩ :=
    Set.ruzsa_covering_add (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne (by convert Z3)
  have A_subset_uH : A ⊆ u + H := by
    refine hAu.trans $ add_subset_add_left $
      (sub_subset_sub (inter_subset_right ..) (inter_subset_right ..)).trans ?_
    rw [add_sub_add_comm, singleton_sub_singleton, sub_self]
    simp
  refine ⟨H, u, ?_, IHA, IAH, A_subset_uH⟩
  rw [←Real.rpow_natCast]; convert hucard; norm_cast

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
    obtain ⟨K, hK, hK'⟩ := S.toFinite.exists_maximalFor (fun K : AddSubgroup G ↦ Nat.card K) S hnon
    simp only [ge_iff_le, Set.mem_setOf_eq, S] at hK
    use K
    refine ⟨hK.2, ?_, hK.1⟩
    rcases LE.le.lt_or_eq hK.1 with heq | heq
    · have hneq : (K:Set G) ≠ (H:Set G) := by
        contrapose! heq
        simp only [SetLike.coe_set_eq] at heq
        simp only [heq, lt_self_iff_false, not_false_eq_true]
      obtain ⟨a, ha, ha'⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hK.1 hneq)
      let Z := AddSubgroup.zmultiples a
      let H' := K ⊔ Z
      contrapose! ha'
      have hcard : Nat.card H' ≤ k := by
        apply le_trans _ ha'
        rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe, AddSubgroup.normal_add K Z, Nat.mul_comm]
        calc
          _ ≤ Nat.card (K : Set G) * Nat.card (Z : Set G) := Set.natCard_add_le
          _ ≤ _ := by
            gcongr
            rw [SetLike.coe_sort_coe, Nat.card_zmultiples a]
            apply addOrderOf_le_of_nsmul_eq_zero (Nat.zero_lt_of_lt hm) (htorsion a)
      have hH' : H' ≤ H := by
        simpa only [sup_le_iff, hK.1, AddSubgroup.zmultiples_le, true_and, H', Z]
      have hsub : (K:Set G) ⊆ (H':Set G) := SetLike.coe_subset_coe.mpr le_sup_left
      have hcard' : Nat.card K ≤ Nat.card H' := by
          rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe, Set.Nat.card_coe_set_eq (K:Set G), Set.Nat.card_coe_set_eq (H':Set G)]
          exact Set.ncard_le_ncard hsub (H' : Set G).toFinite
      have : (K:Set G) = (H':Set G) := by
          apply (Set.subset_iff_eq_of_ncard_le ?_ ?_).mp hsub
          · rw [← Set.Nat.card_coe_set_eq (H':Set G), ← Set.Nat.card_coe_set_eq (K:Set G)]
            exact hK' ⟨hH', hcard⟩ hcard'
          exact Set.toFinite (H':Set G)
      rw [this]
      exact (le_sup_right : AddSubgroup.zmultiples a ≤ H') (AddSubgroup.mem_zmultiples a)
    rw [heq]
    exact lt_of_le_of_lt hk ((Nat.lt_mul_iff_one_lt_left Nat.card_pos).mpr hm)







/--Suppose that $G$ is a finite abelian group of torsion $m$.
  If $A \subset G$ is non-empty and $|A+A| \leq K|A|$, then $A$ can be covered by most $mK^{64m^3+1}$ translates of a subspace $H$ of $G$ with $|H| \leq |A|$.
-/
theorem torsion_PFR {G : Type*} [AddCommGroup G] [Fintype G] {m:ℕ} (hm: m ≥ 2)
     (htorsion : ∀ x:G, m • x = 0) {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty)
     (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < m * K ^ (256*m^3+1) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K := PFR_conjecture_pos_aux' h₀A hA
   -- consider the subgroup `H` given by Lemma `torsion_PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (128 * m^3+1) * Nat.card A ^ (1/2:ℝ) * Nat.card H ^ (-1/2:ℝ)
      ∧ Nat.card H ≤ K ^ (256*m^3) * Nat.card A ∧ Nat.card A ≤ K ^ (256*m^3) * Nat.card H
      ∧ A ⊆ c + H :=
    torsion_PFR_conjecture_aux hm htorsion h₀A hA

  have H_pos : (0 : ℝ) < Nat.card H := by
    have : 0 < Nat.card H := Nat.card_pos; positivity
  rcases le_or_gt (Nat.card H) (Nat.card A) with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ ((128*m^3+1)) * Nat.card A ^ (1/2:ℝ) * Nat.card H ^ (-1/2:ℝ) := hc
    _ ≤ K ^ ((128*m^3+1)) * (K ^ (256*m^3) * Nat.card H) ^ (1/2:ℝ) * Nat.card H ^ (-1/2:ℝ) := by
      gcongr
    _ = K ^ (256*m^3+1) := by
      rpow_ring; norm_num
      simp_rw [←Real.rpow_natCast]
      rw [←Real.rpow_mul (by positivity), ←Real.rpow_add (by positivity)]
      congr; push_cast; ring
    _ < m * K ^ (256*m^3+1) := by
      apply (lt_mul_iff_one_lt_left _).mpr
      · norm_num; linarith [hm]
      positivity
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / m < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : AddSubgroup G, Nat.card H' ≤ Nat.card A
          ∧ Nat.card A < m * Nat.card H' ∧ H' ≤ H := by
      have A_pos' : 0 < Nat.card A := mod_cast A_pos
      exact torsion_exists_subgroup_subset_card_le hm htorsion H h.le A_pos'.ne'
    have : (Nat.card A / m : ℝ) < Nat.card H' := by
      rw [div_lt_iff₀, mul_comm]
      · norm_cast
      norm_cast; exact Nat.zero_lt_of_lt hm
    have H'_pos : (0 : ℝ) < Nat.card H' := by
      have : 0 < Nat.card H' := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ := AddSubgroup.exists_left_transversal_of_le H'H
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast Set.natCard_add_le
    _ ≤ (K ^ ((128*m^3+1)) * Nat.card A ^ (1 / 2:ℝ) * (Nat.card H ^ (-1 / 2:ℝ)))
          * (Nat.card H / Nat.card H') := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ ((128*m^3+1)) * Nat.card A ^ (1 / 2:ℝ) * (Nat.card H ^ (-1 / 2:ℝ)))
          * (Nat.card H / (Nat.card A / m)) := by
        gcongr
    _ = m * K ^ ((128*m^3+1)) * Nat.card A ^ (-1/2:ℝ) * Nat.card H ^ (1/2:ℝ) := by
        field_simp
        rpow_ring
        norm_num
    _ ≤ m * K ^ ((128*m^3+1)) * Nat.card A ^ (-1/2:ℝ) * (K ^ (256*m^3) * Nat.card A) ^ (1/2:ℝ) := by
        gcongr
    _ = m * K ^ (256*m^3+1) := by
        rpow_ring
        norm_num
        left
        simp_rw [←Real.rpow_natCast]
        rw [←Real.rpow_mul (by positivity), ←Real.rpow_add (by positivity)]
        congr; push_cast; ring
