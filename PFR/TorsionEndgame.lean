import Mathlib.Data.Set.Card
import PFR.Main
import PFR.MultiTauFunctional

/-!
# Endgame for the Torsion PFR theorem
-/

open MeasureTheory ProbabilityTheory Set
open scoped Pointwise

section AnalyzeMinimizer

universe u

variable {G Ωₒ : Type u} [MeasureableFinGroup G] [MeasureSpace Ωₒ] {p : multiRefPackage G Ωₒ} {Ω : Fin p.m → Type u}
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

/-- We have `I[Z_1 : Z_2 | W], I[Z_2 : Z_3 | W], I[Z_1 : Z_3 | W] ≤ 4m^2 η k`.
-/
lemma mutual_information_le_t_12 : I[Z1 : Z2 | W] ≤ 4 * p.m ^ 2 * p.η * k := sorry

lemma mutual_information_le_t_13 : I[Z1 : Z3 | W] ≤ 4 * p.m ^ 2 * p.η * k := sorry

lemma mutual_information_le_t_23 : I[Z2 : Z3 | W] ≤ 4 * p.m ^ 2 * p.η * k := sorry

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
      . let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun i ↦ {(i,j')}
        let φ : (i:Fin p.m) → ((_: S i) → G) → G := fun i x ↦ x ⟨ (i,j'), by simp [S] ⟩
        convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with i ω
        rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
        simp [S] at hij; cc
      let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun i ↦ {(i,j)}
      let φ : (i:Fin p.m) → ((_: S i) → G) → G := fun i x ↦ x ⟨ (i,j), by simp [S] ⟩
      convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with i ω
      rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
      simp [S] at hij; cc
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
      convert multidist_ruzsa_IV p.hm (fun i ω ↦ Y (i, j') ω) _ (by simp; fun_prop) (by infer_instance) using 2
      . apply multiDist_copy; intro i; convert (hident i j').symm
      let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun i ↦ {(i,j')}
      let φ : (i:Fin p.m) → ((_: S i) → G) → G := fun i x ↦ x ⟨ (i,j'), by simp [S] ⟩
      convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop) with i ω
      rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
      simp [S] at hij; cc

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
  let S : Fin p.m → Finset (Fin p.m × Fin p.m) := fun i ↦ {(i,j)}
  let φ : (i:Fin p.m) → ((_: S i) → G) → G := fun i x ↦ x ⟨ (i,j), by simp [S] ⟩
  convert iIndepFun.finsets_comp S _ h_indep (by fun_prop) φ (by fun_prop)
  rw [Finset.pairwiseDisjoint_iff]; rintro _ _ _ _ ⟨ ⟨ _, _ ⟩, hij ⟩
  simp [S] at hij; cc

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
  have hm_2 : (p.m:ℝ) ≥ 2 := by norm_cast; exact p.hm
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
            sorry
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
      exact multidist_ruzsa_II p.hm _ hΩ_prob _ hX_mes (by infer_instance)
    _ = 4 * (p.m^3 - p.m^2) * k - 3 * p.m * (2*p.m - 1) * k /2 := by ring
    _ ≤ _ := by
      simp; positivity


/-- Let $G$ be an abelian group, let $(T_1,T_2,T_3)$ be a $G^3$-valued random variable such that $T_1+T_2+T_3=0$ holds identically, and write
  \[
    \delta := \bbI[T_1 : T_2] + \bbI[T_1 : T_3] + \bbI[T_2 : T_3].
  \]
  Let $Y_1,\dots,Y_n$ be some further $G$-valued random variables and let $\alpha>0$ be a constant.
  Then there exists a random variable $U$ such that
$$  d[U;U] + \alpha \sum_{i=1}^n d[Y_i;U] \leq \Bigl(2 + \frac{\alpha n}{2} \Bigr) \delta + \alpha \sum_{i=1}^n d[Y_i;T_2].
$$
-/
lemma dist_of_U_add_le {G: Type*} [MeasureableFinGroup G] {Ω : Type*} [MeasureSpace Ω] (T₁ T₂ T₃ : Ω → G) (hsum: T₁ + T₂ + T₃ = 0) (n:ℕ) {Ω': Fin n → Type*} (hΩ': ∀ i, MeasureSpace (Ω' i)) (Y: ∀ i, (Ω' i) → G) {α:ℝ} (hα: α > 0): ∃ (Ω'':Type*) (hΩ'': MeasureSpace Ω'') (U: Ω'' → G), d[U # U] + α * ∑ i, d[Y i # U] ≤ (2 + α * n / 2) * (I[T₁ : T₂] + I[T₁ : T₃] + I[T₂ : T₃]) + α * ∑ i, d[Y i # T₂] := sorry

/-- We have $k = 0$. -/
lemma k_eq_zero : k = 0 := sorry

end AnalyzeMinimizer

/-- Suppose that $G$ is a finite abelian group of torsion $m$. Suppose that $X$ is a $G$-valued random variable. Then there exists a subgroup $H \leq G$ such that \[ d[X;U_H] \leq 64 m^3 d[X;X].\] -/
lemma dist_of_X_U_H_le {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
  [MeasurableSingletonClass G] (m:ℕ) (hm: m ≥ 2) (htorsion: ∀ x:G, m • x = 0) (Ω : Type*) [MeasureSpace Ω] (X: Ω → G): ∃ H : AddSubgroup G, ∃ Ω' : Type*, ∃ mΩ : MeasureSpace Ω', ∃ U : Ω' → G,
    IsUniform H U ∧ d[X # U] ≤ 64 * m^3 * d[X # X] := sorry

/-- Suppose that $G$ is a finite abelian group of torsion $m$. If $A \subset G$ is non-empty and
  $|A+A| \leq K|A|$, then $A$ can be covered by at most $K ^
  {(64m^3+2)/2}|A|^{1/2}/|H|^{1/2}$ translates of a subspace $H$ of $G$ with
 $|H|/|A| \in [K^{-64m^3}, K^{64m^3}]$
     -/
lemma torsion_PFR_conjecture_aux {G : Type*} [AddCommGroup G] [Fintype G] {m:ℕ} (hm: m ≥ 2)
    (htorsion: ∀ x:G, m • x = 0) {A : Set G} [Finite A] {K : ℝ} (h₀A : A.Nonempty)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (64 * m^3 + 2) * Nat.card A ^ (1/2:ℝ) * Nat.card H ^ (-1/2 : ℝ )
      ∧ Nat.card H ≤ K ^ (64 * m^3) * Nat.card A
      ∧ Nat.card A ≤ K ^ (64 * m^3) * Nat.card H ∧ A ⊆ c + H := sorry

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
      Nat.card c < m * K ^ (96*m^3+2) ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K := PFR_conjecture_pos_aux' h₀A hA
   -- consider the subgroup `H` given by Lemma `torsion_PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ (64 * m^3+2) * Nat.card A ^ (1/2:ℝ) * Nat.card H ^ (-1/2:ℝ)
      ∧ Nat.card H ≤ K ^ (64*m^3) * Nat.card A ∧ Nat.card A ≤ K ^ (64*m^3) * Nat.card H
      ∧ A ⊆ c + H :=
    torsion_PFR_conjecture_aux hm htorsion h₀A hA

  have H_pos : (0 : ℝ) < Nat.card H := by
    have : 0 < Nat.card H := Nat.card_pos; positivity
  rcases le_or_gt (Nat.card H) (Nat.card A) with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ ((64*m^3+2)) * Nat.card A ^ (1/2:ℝ) * Nat.card H ^ (-1/2:ℝ) := hc
    _ ≤ K ^ ((64*m^3+2)) * (K ^ (64*m^3) * Nat.card H) ^ (1/2:ℝ) * Nat.card H ^ (-1/2:ℝ) := by
      gcongr
    _ = K ^ (96*m^3+2) := by
      rpow_ring; norm_num
      simp_rw [←Real.rpow_natCast]
      rw [←Real.rpow_mul (by positivity), ←Real.rpow_add (by positivity)]
      congr; push_cast; ring
    _ < m * K ^ (96*m^3+2) := by
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
    _ ≤ (K ^ ((64*m^3+2)) * Nat.card A ^ (1 / 2:ℝ) * (Nat.card H ^ (-1 / 2:ℝ)))
          * (Nat.card H / Nat.card H') := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ ((64*m^3+2)) * Nat.card A ^ (1 / 2:ℝ) * (Nat.card H ^ (-1 / 2:ℝ)))
          * (Nat.card H / (Nat.card A / m)) := by
        gcongr
    _ = m * K ^ ((64*m^3+2)) * Nat.card A ^ (-1/2:ℝ) * Nat.card H ^ (1/2:ℝ) := by
        field_simp
        rpow_ring
        norm_num
    _ ≤ m * K ^ ((64*m^3+2)) * Nat.card A ^ (-1/2:ℝ) * (K ^ (64*m^3) * Nat.card A) ^ (1/2:ℝ) := by
        gcongr
    _ = m * K ^ (96*m^3+2) := by
        rpow_ring
        norm_num
        left
        simp_rw [←Real.rpow_natCast]
        rw [←Real.rpow_mul (by positivity), ←Real.rpow_add (by positivity)]
        congr; push_cast; ring
