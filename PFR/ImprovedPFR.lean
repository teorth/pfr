import PFR.Main

/-!
# Improved PFR

An improvement to PFR that lowers the exponent from 12 to 11.
-/

/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))

open MeasureTheory ProbabilityTheory

section GeneralInequality
variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [Module (ZMod 2) G] [MeasurableAdd₂ G]

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {Ω₀ : Type*} [MeasureSpace Ω₀] [IsProbabilityMeasure (ℙ : Measure Ω₀)]

variable (Y : Ω₀ → G) (hY : Measurable Y)

variable (Z₁ Z₂ Z₃ Z₄ : Ω → G)
  (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) (hZ₄ : Measurable Z₄)

variable (h_indep : iIndepFun ![Z₁, Z₂, Z₃, Z₄])

local notation3 "Sum" => Z₁ + Z₂ + Z₃ + Z₄

include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
lemma gen_ineq_aux1 :
    d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] ≤ d[Y # Z₁]
      + (d[Z₁ # Z₂] + d[Z₁ # Z₃] + d[Z₂ # Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 2
      + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₁]) / 4 := by
  have hS : Measurable Sum := by fun_prop
  have C : d[Z₁ # Z₃] + d[Z₂ # Z₄] = d[Z₁ + Z₂ # Z₃ + Z₄]
           + d[Z₁|Z₁ + Z₂ # Z₃|Z₃ + Z₄] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum] := by
    have M : d[Z₃ # Z₁] + d[Z₄ # Z₂] = d[Z₃ + Z₄ # Z₁ + Z₂]
           + d[Z₃|Z₃ + Z₄ # Z₁|Z₁ + Z₂] + I[Z₃ + Z₁ : Z₁ + Z₂ | Z₃ + Z₁ + Z₄ + Z₂] := by
      apply sum_of_rdist_eq_char_2 ![Z₃, Z₁, Z₄, Z₂] h_indep.reindex_four_cadb (fun i ↦ ?_)
      fin_cases i <;> assumption
    have J1 : Z₃ + Z₁ + Z₄ + Z₂ = Z₁ + Z₂ + Z₃ + Z₄ := by abel
    have J2 : Z₃ + Z₁ = Z₁ + Z₃ := by abel
    simp_rw [J1, J2] at M
    simpa only [rdist_symm (Y := Z₁), rdist_symm (X := Z₄), rdist_symm (X := Z₃ + Z₄),
      condRuzsaDist_symm (Z := Z₃ + Z₄) (W := Z₁ + Z₂) (by fun_prop) (by fun_prop),
      condMutualInfo_comm (X := Z₁ + Z₃) (Y := Z₁ + Z₂) (by fun_prop) (by fun_prop)] using M
  calc
  d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩]
    ≤ d[Y # Z₁ + Z₂ | Sum] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum]/2 :=
      condRuzsaDist_le'_prod (ℙ : Measure Ω₀) (ℙ : Measure Ω) hY (hZ₁.add hZ₂) (hZ₁.add hZ₃) hS
  _ ≤ d[Y # Z₁ + Z₂] + (d[Z₁ + Z₂ # Z₃ + Z₄] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum]) / 2
        + (H[Z₁ + Z₂] - H[Z₃ + Z₄]) / 4 := by
      have I : IndepFun (Z₁ + Z₂) (Z₃ + Z₄) := by
        exact h_indep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption)
          0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      have J1 : (fun a ↦ Z₁ a + Z₂ a) + (fun a ↦ Z₃ a + Z₄ a) = Sum := by ext; simp; abel
      have J2 : (fun a ↦ Z₁ a + Z₂ a) = Z₁ + Z₂ := rfl
      have J3 : (fun a ↦ Z₃ a + Z₄ a) = Z₃ + Z₄ := rfl
      have A := condRuzsaDist_diff_le''' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY (hZ₁.add hZ₂)
        (hZ₃.add hZ₄) I
      rw [J1, J2, J3] at A
      linarith
  _ ≤ d[Y # Z₁] + (d[Z₁ # Z₂] + d[Z₁ + Z₂ # Z₃ + Z₄] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum]) / 2
        + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₁]) / 4 := by
      have I : IndepFun Z₁ Z₂ := by exact h_indep.indepFun (show 0 ≠ 1 by decide)
      have A := condRuzsaDist_diff_le' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY hZ₁ hZ₂ I
      linarith
  _ = _ := by linarith

include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
lemma gen_ineq_aux2 :
    d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] ≤ d[Y # Z₁]
      + (d[Z₁ # Z₃] + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]) / 2
      + (H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃] + H[Z₁] - H[Z₃]) / 4 := by
  cases nonempty_fintype G
  have hS : Measurable Sum := by fun_prop
  have I : IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩) := by
    refine (h_indep.indepFun_prodMk_prodMk ?_ 0 2 1 3
      (by decide) (by decide) (by decide) (by decide))
    intro i; fin_cases i <;> assumption
  calc
  d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩]
    = d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩] := by
      let e : G × G ≃ G × G :=
        { toFun p := ⟨p.1, p.2 - p.1⟩
          invFun p := ⟨p.1, p.2 + p.1⟩
          left_inv := by intro ⟨a, b⟩; simp
          right_inv := by intro ⟨a, b⟩; simp }
      convert (condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂)
        (⟨Z₁ + Z₃, Sum⟩) e (hZ₁.add hZ₂) ((hZ₁.add hZ₃).prodMk hS)
        (.of_discrete (f := e)) e.injective).symm
      simp only [e, Pi.add_apply, Equiv.coe_fn_mk, Function.comp_apply]
      abel
  _ = ∑ w, (Measure.real ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w})) *
        d[Y ; ℙ # Z₁ + Z₂ ; ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]] := by
    rw [condRuzsaDist'_eq_sum']
    · exact hZ₁.add hZ₂
    · exact (hZ₁.add hZ₃).prodMk (hZ₂.add hZ₄)
  _ ≤ ∑ w, Measure.real ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w}) * (d[Y ; ℙ # Z₁ ; ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]]
      + d[Z₁ ; ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w}] # Z₂ ; ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w}]] / 2
      + H[Z₂ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w] / 4 - H[Z₁ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w] / 4) := by
    apply Finset.sum_le_sum (fun w _h'w ↦ ?_)
    rcases eq_or_ne (Measure.real ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w})) 0 with hw|hw
    · simp [hw]
    gcongr
    have : IsProbabilityMeasure (ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]) := cond_isProbabilityMeasure_of_real hw
    have : IndepFun Z₁ Z₂ (ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w}]) := by
      have E : (⟨Z₁, Z₃⟩)⁻¹' {p | p.1 + p.2 = w.1} ∩ (⟨Z₂, Z₄⟩)⁻¹' {p | p.1 + p.2 = w.2}
        = ⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w} := by aesop
      have I : IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩) (ℙ[|(⟨Z₁, Z₃⟩)⁻¹' {p | p.1 + p.2 = w.1}
          ∩ (⟨Z₂, Z₄⟩)⁻¹' {p | p.1 + p.2 = w.2}]) :=
        I.cond (measurable_add (.singleton w.1))
          (measurable_add (.singleton w.2)) (hZ₁.prodMk hZ₃) (hZ₂.prodMk hZ₄)
      rw [E] at I
      exact I.comp measurable_fst measurable_fst
    have := condRuzsaDist_diff_le' (ℙ : Measure Ω₀) (μ' := ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w])
      hY hZ₁ hZ₂ this
    linarith
  _ = d[Y # Z₁ | Z₁ + Z₃] + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]/2
      + H[Z₂ | Z₂ + Z₄] / 4 - H[Z₁ | Z₁ + Z₃] / 4 := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr
    · rw [← condRuzsaDist'_eq_sum' hZ₁ (by fun_prop)]
      apply condRuszaDist_prod_eq_of_indepFun hY hZ₁ (by fun_prop) (by fun_prop)
      exact I.comp (measurable_fst.prodMk measurable_add) measurable_add
    · simp_rw [← mul_div_assoc, ← Finset.sum_div]
      rw [condRuzsaDist_eq_sum' hZ₁ (by fun_prop) hZ₂ (by fun_prop), Fintype.sum_prod_type]
      congr with x
      congr with y
      have : (⟨Z₁ + Z₃, Z₂ + Z₄⟩) ⁻¹' {(x, y)} = (Z₁ + Z₃) ⁻¹' {x} ∩ (Z₂ + Z₄) ⁻¹' {y} := by
        ext p; simp
      rw [this]
      have J : IndepFun (Z₁ + Z₃) (Z₂ + Z₄) := by exact I.comp measurable_add measurable_add
      rw [J.measureReal_inter_preimage_eq_mul (.singleton x) (.singleton y)]
      rcases eq_or_ne (Measure.real ℙ ((Z₁ + Z₃) ⁻¹' {x})) 0 with h1|h1
      · simp [h1]
      rcases eq_or_ne (Measure.real ℙ ((Z₂ + Z₄) ⁻¹' {y})) 0 with h2|h2
      · simp [h2]
      congr 1
      have A : IdentDistrib Z₁ Z₁ (ℙ[|(Z₁ + Z₃) ⁻¹' {x} ∩ (Z₂ + Z₄) ⁻¹' {y}])
          (ℙ[|(Z₁ + Z₃) ⁻¹' {x}]) := by
        rw [← cond_cond_eq_cond_inter' (by exact hZ₁.add hZ₃ (.singleton _))
          (by exact hZ₂.add hZ₄ (.singleton _)) (by finiteness)]
        have : IsProbabilityMeasure (ℙ[|(Z₁ + Z₃) ⁻¹' {x}]) := cond_isProbabilityMeasure_of_real h1
        apply (IndepFun.identDistrib_cond _ (.singleton _) hZ₁ (by fun_prop) _).symm
        · have : IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩) (ℙ[|(⟨Z₁, Z₃⟩) ⁻¹' {p | p.1 + p.2 = x}]) :=
            I.cond_left (measurable_add (.singleton x))
              (hZ₁.prodMk hZ₃)
          exact this.comp measurable_fst measurable_add
        · rw [cond_apply, J.measure_inter_preimage_eq_mul _ _ (.singleton x) (.singleton y)]
          · simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h1 h2
            simp [h1, h2]
          · exact hZ₁.add hZ₃ (.singleton _)
      have B : IdentDistrib Z₂ Z₂ (ℙ[|(Z₁ + Z₃) ⁻¹' {x} ∩ (Z₂ + Z₄) ⁻¹' {y}])
          (ℙ[|(Z₂ + Z₄) ⁻¹' {y}]) := by
        rw [Set.inter_comm, ← cond_cond_eq_cond_inter' (by exact hZ₂.add hZ₄ (.singleton _))
          (by exact hZ₁.add hZ₃ (.singleton _)) (by finiteness)]
        have : IsProbabilityMeasure (ℙ[|(Z₂ + Z₄) ⁻¹' {y}]) := cond_isProbabilityMeasure_of_real h2
        apply (IndepFun.identDistrib_cond _ (.singleton _) hZ₂ (hZ₁.add hZ₃) _).symm
        · have : IndepFun (⟨Z₂, Z₄⟩) (⟨Z₁, Z₃⟩) (ℙ[|(⟨Z₂, Z₄⟩) ⁻¹' {p | p.1 + p.2 = y}]) :=
            I.symm.cond_left (measurable_add (.singleton y))
              (hZ₂.prodMk hZ₄)
          exact this.comp measurable_fst measurable_add
        · rw [Pi.add_def, cond_apply (hZ₂.add hZ₄ (.singleton y)), ← Pi.add_def, ← Pi.add_def,
            J.symm.measure_inter_preimage_eq_mul _ _ (.singleton _) (.singleton _)]
          simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h1 h2
          simp [h1, h2]
      exact A.rdist_congr B
    · have I1 : H[Z₂ | Z₂ + Z₄] = H[Z₂ | ⟨Z₂ + Z₄, Z₁ + Z₃⟩] := by
        apply (condEntropy_prod_eq_of_indepFun hZ₂ (by fun_prop) (by fun_prop) _).symm
        exact I.symm.comp (measurable_fst.prodMk measurable_add) measurable_add
      have I2 : H[Z₂ | ⟨Z₂ + Z₄, Z₁ + Z₃⟩] = H[Z₂ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩] :=
        condEntropy_of_injective' _ hZ₂ ((hZ₁.add hZ₃).prodMk (hZ₂.add hZ₄))
          _ (Equiv.prodComm G G).injective ((hZ₂.add hZ₄).prodMk (hZ₁.add hZ₃))
      rw [I1, I2, condEntropy_eq_sum_fintype _ _ _ (by fun_prop)]
      simp_rw [← mul_div_assoc, Finset.sum_div]
    · have : H[Z₁ | Z₁ + Z₃] = H[Z₁ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩] := by
        apply (condEntropy_prod_eq_of_indepFun hZ₁ (hZ₁.add hZ₃) (hZ₂.add hZ₄) _).symm
        exact I.comp (measurable_fst.prodMk measurable_add) measurable_add
      rw [this, condEntropy_eq_sum_fintype _ _ _ (by fun_prop)]
      simp_rw [← mul_div_assoc, Finset.sum_div]
  _ ≤ (d[Y # Z₁] + d[Z₁ # Z₃]/2 + H[Z₁]/4 - H[Z₃]/4) + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]/2
      + H[Z₂ | Z₂ + Z₄] / 4 - H[Z₁ | Z₁ + Z₃] / 4 := by
    gcongr
    have I : IndepFun Z₁ Z₃ := by exact h_indep.indepFun (show 0 ≠ 2 by decide)
    have := condRuzsaDist_diff_le''' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY hZ₁ hZ₃ I
    linarith
  _ = _ := by ring

include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
/-- Let `Z₁, Z₂, Z₃, Z₄` be independent `G`-valued random variables, and let `Y` be another
`G`-valued random variable. Set `S := Z₁ + Z₂ + Z₃ + Z₄`. Then
`d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] - d[Y # Z₁] ≤`
`(d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4`
`+ (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4`
`+ (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8`.
-/
lemma gen_ineq_00 : d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] - d[Y # Z₁] ≤
    (d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4
    + (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4
    + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8 := by
  have I1 := gen_ineq_aux1 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep
  have I2 := gen_ineq_aux2 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep
  linarith

include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
/-- Other version of `gen_ineq_00`, in which we switch to the complement in the second term. -/
lemma gen_ineq_01 : d[Y # Z₁ + Z₂ | ⟨Z₂ + Z₄, Sum⟩] - d[Y # Z₁] ≤
    (d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4
    + (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4
    + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8 := by
  convert gen_ineq_00 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep using 2
  let e : G × G ≃ G × G :=
  { toFun p := ⟨p.2 - p.1, p.2⟩
    invFun p := ⟨- p.1 + p.2, p.2⟩
    left_inv := by intro ⟨a, b⟩; simp
    right_inv := by intro ⟨a, b⟩; simp }
  convert (condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂) (⟨Z₁ + Z₃, Sum⟩) e
    (by fun_prop) (by fun_prop) (by fun_prop) e.injective) with p
  simp only [e, Pi.add_apply, Equiv.coe_fn_mk, Function.comp_apply]
  abel

include hY hZ₁ hZ₂ hZ₃ hZ₄ h_indep in
/-- Other version of `gen_ineq_00`, in which we switch to the complement in the first term. -/
lemma gen_ineq_10 : d[Y # Z₃ + Z₄ | ⟨Z₁ + Z₃, Sum⟩] - d[Y # Z₁] ≤
    (d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4
    + (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4
    + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8 := by
  convert gen_ineq_00 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep using 2
  have hS : Measurable Sum := by fun_prop
  let e : G × G ≃ G × G := Equiv.prodComm G G
  have A : e ∘ ⟨Z₁ + Z₃, Sum⟩ = ⟨Sum, Z₁ + Z₃⟩ := by ext p <;> rfl
  rw [← condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₃ + Z₄) (⟨Z₁ + Z₃, Sum⟩)
      e (by fun_prop) (by fun_prop) (by fun_prop) e.injective ,
      ← condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂)
        (⟨Z₁ + Z₃, Sum⟩) e (by fun_prop) (by fun_prop) (by fun_prop) e.injective, A,
      condRuzsaDist'_prod_eq_sum _ _ (by fun_prop) hS (by fun_prop),
      condRuzsaDist'_prod_eq_sum _ _ (by fun_prop) hS (by fun_prop)]
  congr with w
  rcases eq_or_ne (Measure.real ℙ ((Z₁ + Z₃) ⁻¹' {w})) 0 with hw|hw
  · simp [hw]
  have : IsProbabilityMeasure (ℙ[|(Z₁ + Z₃) ⁻¹' {w}]) := cond_isProbabilityMeasure_of_real hw
  have : Sum = (Z₁ + Z₂) + (Z₃ + Z₄) := by abel
  rw [this, condRuzsaDist'_of_inj_map' hY (by fun_prop) (by fun_prop)]

end GeneralInequality

section MainEstimates

open MeasureTheory ProbabilityTheory

variable {G : Type*} [AddCommGroup G] [Finite G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [Module (ZMod 2) G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable {p : refPackage Ω₀₁ Ω₀₂ G}

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {X₁ X₂ X₁' X₂' : Ω → G}
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun ![X₁, X₂, X₂', X₁'])

variable (h_min : tau_minimizes p X₁ X₂)

/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[X₁ # X₂]

/-- `U := X₁ + X₂` -/
local notation3 "U" => X₁ + X₂

/-- `V := X₁' + X₂` -/
local notation3 "V" => X₁' + X₂

/-- `W := X₁' + X₁` -/
local notation3 "W" => X₁' + X₁

/-- `S := X₁ + X₂ + X₁' + X₂'` -/
local notation3 "S" => X₁ + X₂ + X₁' + X₂'

/-- `I₁ := I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₂` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']

/-- `I₂ := I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₁` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₂" => I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']

local notation3:max "c[" A "; " μ " # " B " ; " μ' "]" =>
  d[p.X₀₁; ℙ # A; μ] - d[p.X₀₁ # X₁] + (d[p.X₀₂; ℙ # B; μ'] - d[p.X₀₂ # X₂])

local notation3:max "c[" A " # " B "]" =>
  d[p.X₀₁ # A] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # B] - d[p.X₀₂ # X₂])

local notation3:max "c[" A " | " B " # " C " | " D "]" =>
  d[p.X₀₁ # A|B] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # C|D] - d[p.X₀₂ # X₂])

section aux

variable {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
variable {T₁ T₂ T₃ : Ω' → G} (hT : T₁ + T₂ + T₃ = 0)
variable (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)

local notation3:max "δ[" μ "]" => I[T₁ : T₂ ; μ] + I[T₂ : T₃ ; μ] + I[T₃ : T₁ ; μ]
local notation3:max "δ" => I[T₁ : T₂] + I[T₂ : T₃] + I[T₃ : T₁]

local notation3:max "ψ[" A " # " B "]" => d[A # B] + p.η * (c[A # B])
local notation3:max "ψ[" A "; " μ " # " B " ; " μ' "]" =>
  d[A ; μ # B ; μ'] + p.η * c[A ; μ # B ; μ']

include hT hT₁ hT₂ hT₃ h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
[IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- For any $T_1, T_2, T_3$ adding up to $0$, then $k$ is at most
$$ \delta + \eta (d[X^0_1;T_1|T_3]-d[X^0_1;X_1]) + \eta (d[X^0_2;T_2|T_3]-d[X^0_2;X_2])$$
where $\delta = I[T₁ : T₂ ; μ] + I[T₂ : T₃ ; μ] + I[T₃ : T₁ ; μ]$. -/
lemma construct_good_prelim' : k ≤ δ + p.η * c[T₁ | T₃ # T₂ | T₃] := by
  let sum1 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]
  let sum2 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₁; ℙ # T₁; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₁ # X₁]]
  let sum3 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₂; ℙ # T₂; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₂ # X₂]]
  let sum4 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ ψ[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]
  have h2T₃ : T₃ = T₁ + T₂ := by
    calc T₃ = T₁ + T₂ + T₃ - T₃ := by simp [hT, ZModModule.neg_eq_self]
      _ = T₁ + T₂ := by rw [add_sub_cancel_right]
  have hP : IsProbabilityMeasure (Measure.map T₃ ℙ) :=
    Measure.isProbabilityMeasure_map hT₃.aemeasurable
  -- control sum1 with entropic BSG
  have h1 : sum1 ≤ δ := by
    have h1 : sum1 ≤ 3 * I[T₁ : T₂] + 2 * H[T₃] - H[T₁] - H[T₂] := by
      subst h2T₃; exact ent_bsg hT₁ hT₂
    have h2 : H[⟨T₂, T₃⟩] = H[⟨T₁, T₂⟩] := by
      rw [h2T₃, entropy_add_right', entropy_comm] <;> assumption
    have h3 : H[⟨T₁, T₂⟩] = H[⟨T₃, T₁⟩] := by
      rw [h2T₃, entropy_add_left, entropy_comm] <;> assumption
    simp_rw [mutualInfo_def] at h1 ⊢; linarith
  -- rewrite sum2 and sum3 as Rusza distances
  have h2 : sum2 = d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁] := by
    simp only [sum2, integral_sub .of_finite .of_finite, integral_const, smul_eq_mul]
    simp [condRuzsaDist'_eq_sum hT₁ hT₃,
      integral_eq_setIntegral (FiniteRange.null_of_compl _ T₃), integral_finset _ _ .finset,
      map_measureReal_apply hT₃ (.singleton _), smul_eq_mul]
  have h3 : sum3 = d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂] := by
    simp only [sum3, integral_sub .of_finite .of_finite, integral_const, smul_eq_mul]
    simp [condRuzsaDist'_eq_sum hT₂ hT₃,
      integral_eq_setIntegral (FiniteRange.null_of_compl _ T₃), integral_finset _ _ .finset,
      map_measureReal_apply hT₃ (.singleton _)]
  -- put all these estimates together to bound sum4
  have h4 : sum4 ≤ δ + p.η * ((d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁])
      + (d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂])) := by
    have : sum4 = sum1 + p.η * (sum2 + sum3) := by
      simp only [sum1, sum2, sum3, sum4, integral_add .of_finite .of_finite, integral_const_mul]
    rw [this, h2, h3, add_assoc, mul_add]
    linarith
  have hk : k ≤ sum4 := by
    suffices (Measure.map T₃ ℙ)[fun _ ↦ k] ≤ sum4 by simpa using this
    refine integral_mono_ae .of_finite .of_finite <| ae_iff_of_countable.2 fun t ht ↦ ?_
    have : IsProbabilityMeasure (ℙ[|T₃ ⁻¹' {t}]) :=
      cond_isProbabilityMeasure (by simpa [hT₃] using ht)
    dsimp only
    linarith only [distance_ge_of_min' (μ := ℙ[|T₃ ⁻¹' {t}]) (μ' := ℙ[|T₃ ⁻¹' {t}]) p h_min hT₁ hT₂]
  exact hk.trans h4

open Module

include hT hT₁ hT₂ hT₃ h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
[IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- In fact $k$ is at most
 $$ \delta + \frac{\eta}{6} \sum_{i=1}^2 \sum_{1 \leq j,l \leq 3; j \neq l}
     (d[X^0_i;T_j|T_l] - d[X^0_i; X_i]).$$
-/
lemma construct_good_improved' :
    k ≤ δ + (p.η / 6) *
     ((d[p.X₀₁ # T₁ | T₂] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁])
    + (d[p.X₀₁ # T₂ | T₁] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₂ | T₃] - d[p.X₀₁ # X₁])
    + (d[p.X₀₁ # T₃ | T₁] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₃ | T₂] - d[p.X₀₁ # X₁])
    + (d[p.X₀₂ # T₁ | T₂] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₁ | T₃] - d[p.X₀₂ # X₂])
    + (d[p.X₀₂ # T₂ | T₁] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂])
    + (d[p.X₀₂ # T₃ | T₁] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₃ | T₂] - d[p.X₀₂ # X₂])) := by
  have I1 : I[T₂ : T₁] = I[T₁ : T₂] := mutualInfo_comm hT₂ hT₁ _
  have I2 : I[T₃ : T₁] = I[T₁ : T₃] := mutualInfo_comm hT₃ hT₁ _
  have I3 : I[T₃ : T₂] = I[T₂ : T₃] := mutualInfo_comm hT₃ hT₂ _
  have Z123 := construct_good_prelim' h_min hT hT₁ hT₂ hT₃
  have h132 : T₁ + T₃ + T₂ = 0 := by rw [← hT]; abel
  have Z132 := construct_good_prelim' h_min h132 hT₁ hT₃ hT₂
  have h213 : T₂ + T₁ + T₃ = 0 := by rw [← hT]; abel
  have Z213 := construct_good_prelim' h_min h213 hT₂ hT₁ hT₃
  have h231 : T₂ + T₃ + T₁ = 0 := by rw [← hT]; abel
  have Z231 := construct_good_prelim' h_min h231 hT₂ hT₃ hT₁
  have h312 : T₃ + T₁ + T₂ = 0 := by rw [← hT]; abel
  have Z312 := construct_good_prelim' h_min h312 hT₃ hT₁ hT₂
  have h321 : T₃ + T₂ + T₁ = 0 := by rw [← hT]; abel
  have Z321 := construct_good_prelim' h_min h321 hT₃ hT₂ hT₁
  simp only [I1, I2, I3] at Z123 Z132 Z213 Z231 Z312 Z321
  linarith

include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]
[IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Rephrase `construct_good_improved'` with an explicit probability measure, as we will
apply it to (varying) conditional measures. -/
lemma construct_good_improved'' {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    [IsProbabilityMeasure μ] {T₁ T₂ T₃ : Ω' → G}
    (hT : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) :
    k ≤ I[T₁ : T₂ ; μ] + I[T₂ : T₃ ; μ] + I[T₃ : T₁ ; μ] + (p.η / 6) *
    ((d[p.X₀₁ ; ℙ # T₁ | T₂ ; μ] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ ; ℙ # T₁ | T₃ ; μ] - d[p.X₀₁ # X₁])
      + (d[p.X₀₁ ; ℙ # T₂ | T₁ ; μ] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ ; ℙ # T₂ | T₃ ; μ] - d[p.X₀₁ # X₁])
      + (d[p.X₀₁ ; ℙ # T₃ | T₁ ; μ] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ ; ℙ # T₃ | T₂ ; μ] - d[p.X₀₁ # X₁])
      + (d[p.X₀₂ ; ℙ # T₁ | T₂ ; μ] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ ; ℙ # T₁ | T₃ ; μ] - d[p.X₀₂ # X₂])
      + (d[p.X₀₂ ; ℙ # T₂ | T₁ ; μ] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ ; ℙ # T₂ | T₃ ; μ] - d[p.X₀₂ # X₂])
      + (d[p.X₀₂ ; ℙ # T₃ | T₁ ; μ] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ ; ℙ # T₃ | T₂ ; μ] - d[p.X₀₂ # X₂]))
    := by
  let M : MeasureSpace Ω' := ⟨μ⟩
  exact construct_good_improved' h_min hT hT₁ hT₂ hT₃

end aux

include hX₁ hX₂ hX₁' hX₂' h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] in
/-- $k$ is at most
$$ \leq I(U : V \, | \, S) + I(V : W \, | \,S) + I(W : U \, | \, S) + \frac{\eta}{6}
\sum_{i=1}^2 \sum_{A,B \in \{U,V,W\}: A \neq B} (d[X^0_i;A|B,S] - d[X^0_i; X_i]).$$
-/
lemma averaged_construct_good :
    k ≤ (I[U : V | S] + I[V : W | S] + I[W : U | S]) + p.η / 6 *
      (((d[p.X₀₁ # U | ⟨V, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # U | ⟨W, S⟩] - d[p.X₀₁ # X₁])
      + (d[p.X₀₁ # V | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # V | ⟨W, S⟩] - d[p.X₀₁ # X₁])
      + (d[p.X₀₁ # W | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # W | ⟨V, S⟩] - d[p.X₀₁ # X₁]))
      + ((d[p.X₀₂ # U | ⟨V, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # U | ⟨W, S⟩] - d[p.X₀₂ # X₂])
      + (d[p.X₀₂ # V | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # V | ⟨W, S⟩] - d[p.X₀₂ # X₂])
      + (d[p.X₀₂ # W | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # W | ⟨V, S⟩] - d[p.X₀₂ # X₂])))
    := by
  cases nonempty_fintype G
  have hS : Measurable S := by fun_prop
  have hU : Measurable U := by fun_prop
  have hV : Measurable V := by fun_prop
  have hW : Measurable W := by fun_prop
  have hUVW : U + V + W = 0 := sum_uvw_eq_zero X₁ X₂ X₁'
  have hz (a : ℝ) : a = ∑ z, (Measure.real ℙ (S ⁻¹' {z})) * a := by
    rw [← Finset.sum_mul, sum_measureReal_preimage_singleton]
    · simp only [Finset.coe_univ, Set.preimage_univ, probReal_univ, one_mul]
    · intro y hy
      apply hS
      exact measurableSet_singleton y
  rw [hz k, hz (d[p.X₀₁ # X₁]), hz (d[p.X₀₂ # X₂])]
  simp only [condMutualInfo_eq_sum' hS, ← Finset.sum_add_distrib, ← mul_add,
    condRuzsaDist'_prod_eq_sum', hU, hS, hV, hW, ← Finset.sum_sub_distrib, ← mul_sub,
      mul_comm (p.η/6)]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum (fun i _hi ↦ ?_)
  rcases eq_or_ne (Measure.real ℙ (S ⁻¹' {i})) 0 with h'i|h'i
  · simp [h'i]
  rw [mul_assoc, ← mul_add]
  gcongr
  have : IsProbabilityMeasure (ℙ[|S ⁻¹' {i}]) := cond_isProbabilityMeasure_of_real h'i
  linarith [construct_good_improved'' h_min (ℙ[|S ⁻¹' {i}]) hUVW hU hV hW]

variable (p)

include hX₁ hX₂ hX₁' hX₂' h_indep h₁ h₂ in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] in
lemma dist_diff_bound_1 :
      (d[p.X₀₁ # U | ⟨V, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # U | ⟨W, S⟩] - d[p.X₀₁ # X₁])
    + (d[p.X₀₁ # V | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # V | ⟨W, S⟩] - d[p.X₀₁ # X₁])
    + (d[p.X₀₁ # W | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # W | ⟨V, S⟩] - d[p.X₀₁ # X₁])
    ≤ (16 * k + 6 * d[X₁ # X₁] + 2 * d[X₂ # X₂]) / 4 + (H[X₁ + X₁'] - H[X₂ + X₂']) / 4
      + (H[X₂ | X₂ + X₂'] - H[X₁ | X₁ + X₁']) / 4 := by
  have I1 := gen_ineq_01 p.X₀₁ p.hmeas1 X₁ X₂ X₂' X₁' hX₁ hX₂ hX₂' hX₁' h_indep.reindex_four_abcd
  have I2 := gen_ineq_00 p.X₀₁ p.hmeas1 X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h_indep.reindex_four_abdc
  have I3 := gen_ineq_10 p.X₀₁ p.hmeas1 X₁ X₂' X₂ X₁' hX₁ hX₂' hX₂ hX₁' h_indep.reindex_four_acbd
  have I4 := gen_ineq_10 p.X₀₁ p.hmeas1 X₁ X₂' X₁' X₂ hX₁ hX₂' hX₁' hX₂ h_indep.reindex_four_acdb
  have I5 := gen_ineq_00 p.X₀₁ p.hmeas1 X₁ X₁' X₂ X₂' hX₁ hX₁' hX₂ hX₂' h_indep.reindex_four_adbc
  have I6 := gen_ineq_01 p.X₀₁ p.hmeas1 X₁ X₁' X₂' X₂ hX₁ hX₁' hX₂' hX₂ h_indep.reindex_four_adcb
  have C1 : U + X₂' + X₁' = S := by abel
  have C2 : W + X₂ + X₂' = S := by abel
  have C3 : X₁ + X₂' + X₂ + X₁' = S := by abel
  have C4 : X₁ + X₂' + X₁' + X₂ = S := by abel
  have C5 : W + X₂' + X₂ = S := by abel
  have C7 : X₂ + X₁' = V := by abel
  have C8 : X₁ + X₁' = W := by abel
  have C9 : d[X₁ # X₂'] = d[X₁ # X₂] := h₂.symm.rdist_congr_right hX₁.aemeasurable
  have C10 : d[X₂ # X₁'] = d[X₁' # X₂] := rdist_symm
  have C11 : d[X₁ # X₁'] = d[X₁ # X₁] := h₁.symm.rdist_congr_right hX₁.aemeasurable
  have C12 : d[X₁' # X₂'] = d[X₁ # X₂] := h₁.symm.rdist_congr h₂.symm
  have C13 : d[X₂ # X₂'] = d[X₂ # X₂] := h₂.symm.rdist_congr_right hX₂.aemeasurable
  have C14 : d[X₁' # X₂] = d[X₁ # X₂] := h₁.symm.rdist_congr_left hX₂.aemeasurable
  have C15 : H[X₁' + X₂'] = H[U] := by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    have I : IdentDistrib (⟨X₁, X₂⟩) (⟨X₁', X₂'⟩) := h₁.prodMk h₂ (h_indep.indepFun zero_ne_one)
        (h_indep.indepFun (show 3 ≠ 2 by decide))
    exact I.symm.comp measurable_add
  have C16 : H[X₂'] = H[X₂] := h₂.symm.entropy_congr
  have C17 : H[X₁'] = H[X₁] := h₁.symm.entropy_congr
  have C18 : d[X₂' # X₁'] = d[X₁' # X₂'] := rdist_symm
  have C19 : H[X₂' + X₁'] = H[U] := by rw [add_comm]; exact C15
  have C20 : d[X₂' # X₂] = d[X₂ # X₂] := h₂.symm.rdist_congr_left hX₂.aemeasurable
  have C21 : H[V] = H[U] := by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) := by
      apply h₁.symm.prodMk (.refl hX₂.aemeasurable)
        (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C22 : H[X₁ + X₂'] = H[X₁ + X₂] := by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) := by
      apply (IdentDistrib.refl hX₁.aemeasurable).prodMk h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C23 : X₂' + X₂ = X₂ + X₂' := by abel
  have C24 : H[X₁ | X₁ + X₂'] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁ (hX₁.add hX₂') hX₁ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) := by
      exact (IdentDistrib.refl hX₁.aemeasurable).prodMk h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C25 : H[X₂ | V] = H[X₂ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₂ (hX₁'.add hX₂) hX₂ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) := by
      exact h₁.symm.prodMk (IdentDistrib.refl hX₂.aemeasurable)
        (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prodMk measurable_add)
  have C26 : H[X₂' | X₂' + X₁'] = H[X₂ | X₁ + X₂] := by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁'.add hX₂') hX₂ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) := h₁.symm.prodMk h₂.symm
        (h_indep.indepFun (show 3 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prodMk measurable_add)
  have C27 : H[X₂' | X₂ + X₂'] = H[X₂ | X₂ + X₂'] := by
    conv_lhs => rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₂'.add hX₂) hX₂ (hX₂.add hX₂')
    have I : IdentDistrib (⟨X₂', X₂⟩) (⟨X₂, X₂'⟩) := h₂.symm.prodMk h₂
        (h_indep.indepFun (show 2 ≠ 1 by decide)) (h_indep.indepFun (show 1 ≠ 2 by decide))
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C28 : H[X₁' | X₁' + X₂'] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add hX₂') hX₁ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) := h₁.symm.prodMk h₂.symm
        (h_indep.indepFun (show 3 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C29 : H[X₁' | V] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add hX₂) hX₁ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) :=
      h₁.symm.prodMk (IdentDistrib.refl hX₂.aemeasurable)
      (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C30 : H[X₂ | X₁ + X₂] = H[X₁ | X₁ + X₂] := by
    have := condEntropy_of_injective ℙ hX₁ (hX₁.add hX₂) _ (fun p ↦ add_right_injective p)
    convert this with ω
    simp [add_comm (X₁ ω), add_assoc (X₂ ω), ZModModule.add_self]
  simp only [C1, C2, C3, C4, C5, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19,
    C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30] at I1 I2 I3 I4 I5 I6 ⊢
  linarith only [I1, I2, I3, I4, I5, I6]

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
omit [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] in
lemma dist_diff_bound_2 :
      ((d[p.X₀₂ # U | ⟨V, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # U | ⟨W, S⟩] - d[p.X₀₂ # X₂])
    + (d[p.X₀₂ # V | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # V | ⟨W, S⟩] - d[p.X₀₂ # X₂])
    + (d[p.X₀₂ # W | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # W | ⟨V, S⟩] - d[p.X₀₂ # X₂]))
    ≤ (16 * k + 6 * d[X₂ # X₂] + 2 * d[X₁ # X₁]) / 4 + (H[X₂ + X₂'] - H[X₁ + X₁']) / 4
      + (H[X₁ | X₁ + X₁'] - H[X₂ | X₂ + X₂']) / 4 := by
  have I1 := gen_ineq_01 p.X₀₂ p.hmeas2 X₂ X₁ X₂' X₁' hX₂ hX₁ hX₂' hX₁' h_indep.reindex_four_bacd
  have I2 := gen_ineq_00 p.X₀₂ p.hmeas2 X₂ X₁ X₁' X₂' hX₂ hX₁ hX₁' hX₂' h_indep.reindex_four_badc
  have I3 := gen_ineq_10 p.X₀₂ p.hmeas2 X₂ X₂' X₁ X₁' hX₂ hX₂' hX₁ hX₁' h_indep.reindex_four_bcad
  have I4 := gen_ineq_10 p.X₀₂ p.hmeas2 X₂ X₂' X₁' X₁ hX₂ hX₂' hX₁' hX₁ h_indep.reindex_four_bcda
  have I5 := gen_ineq_00 p.X₀₂ p.hmeas2 X₂ X₁' X₁ X₂' hX₂ hX₁' hX₁ hX₂' h_indep.reindex_four_bdac
  have I6 := gen_ineq_01 p.X₀₂ p.hmeas2 X₂ X₁' X₂' X₁ hX₂ hX₁' hX₂' hX₁ h_indep.reindex_four_bdca
  have C1 : X₂ + X₁ = X₁ + X₂ := by abel
  have C2 : X₁ + X₁' = W := by abel
  have C3 : U + X₂' + X₁' = S := by abel
  have C4 : X₂ + X₁' = V := by abel
  have C5 : X₂ + X₂' + X₁ + X₁' = S := by abel
  have C6 : X₂ + X₂' + X₁' + X₁ = S := by abel
  have C7 : V + X₁ + X₂' = S := by abel
  have C8 : V + X₂' + X₁ = S := by abel
  have C9 : d[X₂ # X₁] = d[X₁ # X₂] := rdist_symm
  have C10 : d[X₁ # X₂'] = d[X₁ # X₂] := h₂.symm.rdist_congr_right hX₁.aemeasurable
  have C11 : d[X₂ # X₁'] = d[X₁ # X₂] := by
    rw [rdist_symm]
    exact h₁.symm.rdist_congr_left hX₂.aemeasurable
  have C12 : d[X₂' # X₁'] = d[X₁' # X₂'] := rdist_symm
  have C13 : d[X₂' # X₁] = d[X₁ # X₂'] := rdist_symm
  have C14 : d[X₁' # X₁] = d[X₁ # X₁'] := rdist_symm
  have C15 : d[X₁' # X₂'] = d[X₁ # X₂] := h₁.symm.rdist_congr h₂.symm
  have C16 : H[X₁' + X₂'] = H[X₁ + X₂] := by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    have I : IdentDistrib (⟨X₁, X₂⟩) (⟨X₁', X₂'⟩) := h₁.prodMk h₂ (h_indep.indepFun zero_ne_one)
        (h_indep.indepFun (show 3 ≠ 2 by decide))
    exact I.symm.comp measurable_add
  have C17 : H[X₂' + X₁'] = H[X₁ + X₂] := by rw [add_comm]; exact C16
  have C18 : H[X₁'] = H[X₁] := h₁.symm.entropy_congr
  have C19 : H[X₂'] = H[X₂] := h₂.symm.entropy_congr
  have C20 : H[X₁ + X₂'] = H[X₁ + X₂] := by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) :=
      (IdentDistrib.refl hX₁.aemeasurable).prodMk h₂.symm
      (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C21 : H[X₁' | W] = H[X₁ | W] := by
    conv_rhs => rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add hX₁) hX₁ (hX₁.add hX₁')
    have I : IdentDistrib (⟨X₁', X₁⟩) (⟨X₁, X₁'⟩) := h₁.symm.prodMk h₁
        (h_indep.indepFun (show 3 ≠ 0 by decide)) (h_indep.indepFun (show 0 ≠ 3 by decide))
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C22 : H[X₂' | X₂' + X₁] = H[X₂ | X₁ + X₂] := by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁.add hX₂') hX₂ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) :=
      (IdentDistrib.refl hX₁.aemeasurable).prodMk h₂.symm
      (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prodMk measurable_add)
  have C23 : H[X₁ | X₁ + X₂'] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁ (hX₁.add hX₂') hX₁ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) :=
      (IdentDistrib.refl hX₁.aemeasurable).prodMk h₂.symm
      (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C24 : H[X₂ | V] = H[X₂ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₂ (hX₁'.add hX₂) hX₂ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) :=
      h₁.symm.prodMk (IdentDistrib.refl hX₂.aemeasurable)
      (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prodMk measurable_add)
  have C25 : H[X₂' | X₂' + X₁'] = H[X₂ | X₁ + X₂] := by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁'.add hX₂') hX₂ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) := h₁.symm.prodMk h₂.symm
        (h_indep.indepFun (show 3 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prodMk measurable_add)
  have C26 : H[X₁' | X₁' + X₂'] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add hX₂') hX₁ (hX₁.add hX₂)
    have I : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) := h₁.symm.prodMk h₂.symm
      (h_indep.indepFun (show 3 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prodMk measurable_add)
  have C27 : H[X₂ | X₁ + X₂] = H[X₁ | X₁ + X₂] := by
    have := condEntropy_of_injective ℙ hX₁ (hX₁.add hX₂) _ (fun p ↦ add_right_injective p)
    convert this with ω
    simp [add_comm (X₁ ω), add_assoc (X₂ ω), ZModModule.add_self]
  have C28 : H[V] = H[U] := by
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) :=
      h₁.symm.prodMk (IdentDistrib.refl hX₂.aemeasurable)
      (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C29 : H[X₂' + X₁] = H[X₁ + X₂] := by
    rw [add_comm]
    apply ProbabilityTheory.IdentDistrib.entropy_congr
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) :=
      (IdentDistrib.refl hX₁.aemeasurable).prodMk h₂.symm
      (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C30 : d[X₁ # X₁'] = d[X₁ # X₁] := h₁.symm.rdist_congr_right hX₁.aemeasurable
  have C31 : d[X₂ # X₂'] = d[X₂ # X₂] := h₂.symm.rdist_congr_right hX₂.aemeasurable
  simp only [C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19,
    C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31]
    at I1 I2 I3 I4 I5 I6 ⊢
  linarith only [I1, I2, I3, I4, I5, I6]

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min in
lemma averaged_final : k ≤ (6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁))
    + p.η / 6 * (8 * k + 2 * (d[X₁ # X₁] + d[X₂ # X₂])) := by
  apply (averaged_construct_good hX₁ hX₂ hX₁' hX₂' h_min).trans
  have : 0 ≤ p.η := p.hη.le
  have := sum_condMutual_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep.reindex_four_abdc h_min
  gcongr ?_ + (p.η / 6) * ?_
  linarith [dist_diff_bound_1 p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep,
    dist_diff_bound_2 p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep]

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min in
/-- Suppose $0 < \eta < 1/8$. Let $X_1, X_2$ be tau-minimizers. Then $d[X_1;X_2] = 0$. The proof
of this lemma uses copies `X₁', X₂'` already in the context. For a version that does not assume
these are given and constructs them instead, use `tau_strictly_decreases'`.
-/
theorem tau_strictly_decreases_aux' (hp : 8 * p.η < 1) : d[X₁ # X₂] = 0 := by
  have : 0 < p.η := p.hη
  have : k ≤ 8 * p.η * k := by calc
    k ≤ (6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁))
        + p.η / 6 * (8 * k + 2 * (d[X₁ # X₁] + d[X₂ # X₂])) :=
      averaged_final p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
    _ ≤ 6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁) +
        p.η / 6 * (8 * k + 2 * (2 * (k + (2 * p.η * k - I₁) / (1 - p.η)))) := by
      gcongr
      exact second_estimate_aux p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂
        h_indep.reindex_four_abdc h_min
    _ = 8 * p.η * k - (1 - 5 * p.η - 4/6 * p.η) * (2 * p.η * k - I₁) / (1 - p.η) := by ring
    _ ≤ 8 * p.η * k := by
      simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
      apply div_nonneg _ (by linarith)
      apply mul_nonneg (by linarith) _
      linarith [first_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min]
  apply le_antisymm _ (rdist_nonneg hX₁ hX₂)
  nlinarith

include hX₁ hX₂ h_min in
theorem tau_strictly_decreases' (hp : 8 * p.η < 1) : d[X₁ # X₂] = 0 := by
  let ⟨A, mA, μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1', h_id2'⟩
    := independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_congr h_id2]
  let _ : MeasureSpace A := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure A) := hμ
  rw [← h_id1.tau_minimizes p h_id2] at h_min
  exact tau_strictly_decreases_aux' p hY₁ hY₂ hY₁' hY₂' (h_id1.trans h_id1'.symm)
    (h_id2.trans h_id2'.symm) h_indep.reindex_four_abdc h_min hp

end MainEstimates

section EntropicPFR

open MeasureTheory ProbabilityTheory
universe uG

open scoped Topology
open Filter Set

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable {G : Type uG} [AddCommGroup G] [Module (ZMod 2) G] [Finite G] [MeasurableSpace G]
  [MeasurableSingletonClass G]
variable (p : refPackage Ω₀₁ Ω₀₂ G)

/-- For `p.η ≤ 1/8`, there exist τ-minimizers `X₁, X₂` at zero Rusza distance. For `p.η < 1/8`,
all minimizers are fine, by `tau_strictly_decreases'`. For `p.η = 1/8`, we use a limit of
minimizers for `η < 1/8`, which exists by compactness. -/
lemma tau_minimizer_exists_rdist_eq_zero :
    ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
      Measurable X₁ ∧ Measurable X₂ ∧ IsProbabilityMeasure (ℙ : Measure Ω) ∧ tau_minimizes p X₁ X₂
      ∧ d[X₁ # X₂] = 0 := by
  -- let `uₙ` be a sequence converging from below to `η`. In particular, `uₙ < 1/8`.
  obtain ⟨u, -, u_mem, u_lim⟩ :
      ∃ u, StrictMono u ∧ (∀ (n : ℕ), u n ∈ Set.Ioo 0 p.η) ∧ Tendsto u atTop (𝓝 p.η) :=
    exists_seq_strictMono_tendsto' p.hη
  -- For each `n`, consider a minimizer associated to `η = uₙ`.
  let q : ℕ → refPackage Ω₀₁ Ω₀₂ G := fun n ↦
    ⟨p.X₀₁, p.X₀₂, p.hmeas1, p.hmeas2, u n, (u_mem n).1, by linarith [(u_mem n).2, p.hη']⟩
  have : ∀ n, ∃ (μ : Measure G × Measure G),
    IsProbabilityMeasure μ.1 ∧ IsProbabilityMeasure μ.2 ∧
      ∀ (ν₁ : Measure G) (ν₂ : Measure G), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      τ[id ; μ.1 # id ; μ.2 | q n] ≤ τ[id ; ν₁ # id ; ν₂ | q n] :=
    fun n ↦ tau_min_exists_measure (q n)
  choose μ μ1_prob μ2_prob hμ using this
  -- The minimizer associated to `uₙ` is at zero Rusza distance of itself, by
  -- lemma `tau_strictly_decreases'`.
  have I n : d[id ; (μ n).1 # id ; (μ n).2] = 0 := by
    let M : MeasureSpace (G × G) := ⟨(μ n).1.prod (μ n).2⟩
    have : IsProbabilityMeasure ((μ n).1.prod (μ n).2) := by infer_instance
    have : d[@Prod.fst G G # @Prod.snd G G] = d[id ; (μ n).1 # id ; (μ n).2] :=
      IdentDistrib.rdist_congr IdentDistrib.fst_id IdentDistrib.snd_id
    rw [← this]
    apply tau_strictly_decreases' (q n) measurable_fst measurable_snd ?_
      (by linarith [(u_mem n).2, p.hη'])
    intro ν₁ ν₂ h₁ h₂
    have A : τ[@Prod.fst G G # @Prod.snd G G | q n] = τ[id ; (μ n).1 # id ; (μ n).2 | q n] :=
      ProbabilityTheory.IdentDistrib.tau_eq (q n) IdentDistrib.fst_id IdentDistrib.snd_id
    rw [A]
    exact hμ n _ _ h₁ h₂
  -- extract a converging subsequence of the sequence of minimizers, seen as pairs of probability
  -- measures on `G` (which is a compact space).
  let μ' : ℕ → ProbabilityMeasure G × ProbabilityMeasure G :=
    fun n ↦ (⟨(μ n).1, μ1_prob n⟩, ⟨(μ n).2, μ2_prob n⟩)
  let _i : TopologicalSpace G := (⊥ : TopologicalSpace G)
  have : DiscreteTopology G := ⟨rfl⟩
  -- The limiting pair of measures will be the desired minimizer.
  rcases IsCompact.tendsto_subseq (x := μ') isCompact_univ (fun n ↦ mem_univ _)
    with ⟨ν, -, φ, φmono, hν⟩
  have φlim : Tendsto φ atTop atTop := φmono.tendsto_atTop
  let M : MeasureSpace (G × G) := ⟨(ν.1 : Measure G).prod ν.2⟩
  have P : IsProbabilityMeasure ((ν.1 : Measure G).prod (ν.2 : Measure G)) := by infer_instance
  refine ⟨G × G, M, Prod.fst, Prod.snd, measurable_fst, measurable_snd, P, ?_, ?_⟩
  -- check that it is indeed a minimizer, as a limit of minimizers.
  · intro ν₁ ν₂ h₁ h₂
    have A : τ[@Prod.fst G G # @Prod.snd G G | p] = τ[id ; ν.1 # id ; ν.2 | p] :=
      ProbabilityTheory.IdentDistrib.tau_eq p IdentDistrib.fst_id IdentDistrib.snd_id
    rw [A]
    have L1 : Tendsto (fun n ↦ τ[id ; (μ (φ n)).1 # id ; (μ (φ n)).2 | q (φ n)]) atTop
        (𝓝 (τ[id ; ν.1 # id ; ν.2 | p])) := by
      apply Tendsto.add (Tendsto.add ?_ (Tendsto.mul (u_lim.comp φlim) ?_))
          (Tendsto.mul (u_lim.comp φlim) ?_)
      · apply Tendsto.comp (continuous_rdist_restrict_probabilityMeasure.tendsto _) hν
      · have : Continuous
          (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ d[p.X₀₁ ; ℙ # id ; μ.1]) :=
        Continuous.comp (continuous_rdist_restrict_probabilityMeasure₁' _ _ p.hmeas1) continuous_fst
        apply Tendsto.comp (this.tendsto _) hν
      · have : Continuous
          (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ d[p.X₀₂ ; ℙ # id ; μ.2]) :=
        Continuous.comp (continuous_rdist_restrict_probabilityMeasure₁' _ _ p.hmeas2) continuous_snd
        apply Tendsto.comp (this.tendsto _) hν
    have L2 : Tendsto (fun n ↦ τ[id ; ν₁ # id ; ν₂ | q (φ n)]) atTop
        (𝓝 (τ[id ; ν₁ # id ; ν₂ | p])) :=
      Tendsto.add (Tendsto.add tendsto_const_nhds (Tendsto.mul (u_lim.comp φlim)
        tendsto_const_nhds)) (Tendsto.mul (u_lim.comp φlim) tendsto_const_nhds)
    exact le_of_tendsto_of_tendsto' L1 L2 (fun n ↦ hμ (φ n) _ _ h₁ h₂)
  -- check that it has zero Rusza distance, as a limit of a sequence at zero Rusza distance.
  · have : d[@Prod.fst G G # @Prod.snd G G] = d[id ; ν.1 # id ; ν.2] :=
      IdentDistrib.rdist_congr IdentDistrib.fst_id IdentDistrib.snd_id
    rw [this]
    have L1 : Tendsto (fun n ↦ d[id ; (μ (φ n)).1 # id ; (μ (φ n)).2]) atTop
      (𝓝 (d[id ; ν.1 # id ; (ν.2 : Measure G)])) := by
        apply Tendsto.comp (continuous_rdist_restrict_probabilityMeasure.tendsto _) hν
    have L2 : Tendsto (fun n ↦ d[id ; (μ (φ n)).1 # id ; (μ (φ n)).2]) atTop (𝓝 0) := by simp [I]
    exact tendsto_nhds_unique L1 L2

/-- `entropic_PFR_conjecture_improv`: For two $G$-valued random variables $X^0_1, X^0_2$, there is
some subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 10 d[X^0_1;X^0_2]$. -/
theorem entropic_PFR_conjecture_improv (hpη : p.η = 1 / 8) :
    ∃ (H : Submodule (ZMod 2) G) (Ω : Type uG) (mΩ : MeasureSpace Ω) (U : Ω → G),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ d[p.X₀₁ # U] + d[p.X₀₂ # U] ≤ 10 * d[p.X₀₁ # p.X₀₂] := by
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, hP, htau_min, hdist⟩ := tau_minimizer_exists_rdist_eq_zero p
  obtain ⟨H, U, hU, hH_unif, hdistX₁, hdistX₂⟩ := exists_isUniform_of_rdist_eq_zero hX₁ hX₂ hdist
  refine ⟨AddSubgroup.toZModSubmodule 2 H, Ω', inferInstance, U, inferInstance, hU, hH_unif , ?_⟩
  have h : τ[X₁ # X₂ | p] ≤ τ[p.X₀₂ # p.X₀₁ | p] := is_tau_min p htau_min p.hmeas2 p.hmeas1
  rw [tau, tau, hpη] at h
  norm_num at h
  have : d[p.X₀₁ # p.X₀₂] = d[p.X₀₂ # p.X₀₁] := rdist_symm
  have : d[p.X₀₁ # U] ≤ d[p.X₀₁ # X₁] + d[X₁ # U] := rdist_triangle p.hmeas1 hX₁ hU
  have : d[p.X₀₂ # U] ≤ d[p.X₀₂ # X₂] + d[X₂ # U] := rdist_triangle p.hmeas2 hX₂ hU
  linarith

/-- `entropic_PFR_conjecture_improv'`: For two $G$-valued random variables $X^0_1, X^0_2$, there is
some subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 10 d[X^0_1;X^0_2]$., and
d[X^0_1; U_H] and d[X^0_2; U_H] are at most 5/2 * d[X^0_1;X^0_2] -/
theorem entropic_PFR_conjecture_improv' (hpη : p.η = 1 / 8) :
    ∃ H : AddSubgroup G, ∃ Ω : Type uG, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ d[p.X₀₁ # U] + d[p.X₀₂ # U] ≤ 10 * d[p.X₀₁ # p.X₀₂] ∧ d[p.X₀₁ # U]
      ≤ 11/2 * d[p.X₀₁ # p.X₀₂] ∧ d[p.X₀₂ # U] ≤ 11/2 * d[p.X₀₁ # p.X₀₂] := by
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, hP, htau_min, hdist⟩ := tau_minimizer_exists_rdist_eq_zero p
  obtain ⟨H, U, hU, hH_unif, hdistX₁, hdistX₂⟩ := exists_isUniform_of_rdist_eq_zero hX₁ hX₂ hdist
  have : d[p.X₀₁ # p.X₀₂] = d[p.X₀₂ # p.X₀₁] := rdist_symm
  have goal₁ : d[p.X₀₁ # U] + d[p.X₀₂ # U] ≤ 10 * d[p.X₀₁ # p.X₀₂] := by
    have h : τ[X₁ # X₂ | p] ≤ τ[p.X₀₂ # p.X₀₁ | p] := is_tau_min p htau_min p.hmeas2 p.hmeas1
    rw [tau, tau, hpη] at h
    norm_num at h
    have : d[p.X₀₁ # U] ≤ d[p.X₀₁ # X₁] + d[X₁ # U] := rdist_triangle p.hmeas1 hX₁ hU
    have : d[p.X₀₂ # U] ≤ d[p.X₀₂ # X₂] + d[X₂ # U] := rdist_triangle p.hmeas2 hX₂ hU
    linarith
  have : d[p.X₀₁ # U] ≤ d[p.X₀₁ # p.X₀₂] + d[p.X₀₂ # U] := rdist_triangle p.hmeas1 p.hmeas2 hU
  have : d[p.X₀₂ # U] ≤ d[p.X₀₂ # p.X₀₁] + d[p.X₀₁ # U] := rdist_triangle p.hmeas2 p.hmeas1 hU
  refine ⟨H, Ω', inferInstance, U, inferInstance, hU, hH_unif, goal₁, by linarith, by linarith⟩

end EntropicPFR

section PFR

open Pointwise Set MeasureTheory ProbabilityTheory Real Fintype Function

variable {G Ω : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Finite G]
    {A B : Set G} {K : ℝ}

/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup $H$
such that $A$ can be covered by at most $K^6 |A|^{1/2} / |H|^{1/2}$ cosets of $H$, and $H$ has
the same cardinality as $A$ up to a multiplicative factor $K^10$. -/
lemma PFR_conjecture_improv_aux (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * A.ncard) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c ≤ K ^ 6 * A.ncard ^ (1/2) * (H : Set G).ncard ^ (-1/2) ∧
      (H : Set G).ncard ≤ K ^ 10 * A.ncard ∧
      A.ncard ≤ K ^ 10 * (H : Set G).ncard ∧ A ⊆ c + H := by
  have A_fin : Finite A := by infer_instance
  classical
  let mG : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := ⟨fun _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' (Set.toFinite _) h₀A hA
  let A' := A.toFinite.toFinset
  have h₀A' : Finset.Nonempty A' := by simpa [A', Finset.Nonempty]
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' h₀A' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -⟩
  rw [hAA'] at UAunif
  have hadd_sub : A + A = A - A := by ext; simp [mem_add, mem_sub, ZModModule.sub_eq_add]
  rw [hadd_sub] at hA
  have : d[UA # UA] ≤ log K := rdist_le_of_isUniform_of_card_add_le h₀A hA UAunif UAmeas
  rw [← hadd_sub] at hA
  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas, 1/8, (by norm_num), (by norm_num)⟩
  -- entropic PFR gives a subgroup `H` which is close to `A` for the Rusza distance
  rcases entropic_PFR_conjecture_improv p (by norm_num)
    with ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm .of_discrete
  have VA'unif := VAunif
  rw [← hAA'] at VA'unif
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm .of_discrete
  let H' := (H : Set G).toFinite.toFinset
  have hHH' : H' = (H : Set G) := Finite.coe_toFinset (toFinite (H : Set G))
  have VH'unif := VHunif
  rw [← hHH'] at VH'unif
  have H_fin : Finite (H : Set G) := by infer_instance
  have : d[VA # VH] ≤ 5 * log K := by rw [idVA.rdist_congr idVH]; linarith
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos
    positivity
  have VA_ent : H[VA] = log A.ncard := VAunif.entropy_eq' A_fin VAmeas
  have VH_ent : H[VH] = log ((H : Set G).ncard) := VHunif.entropy_eq' H_fin VHmeas
  have Icard : |log A.ncard - log ((H : Set G).ncard)| ≤ 10 * log K := by
    rw [← VA_ent, ← VH_ent]
    apply (diff_ent_le_rdist VAmeas VHmeas).trans
    linarith
  have IAH : A.ncard ≤ K ^ 10 * (H : Set G).ncard := by
    have : log A.ncard ≤ log K * 10 + log ((H : Set G).ncard) := by
      linarith [(le_abs_self _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log A_pos).symm
    · rw [exp_add, exp_log H_pos, ← rpow_def_of_pos K_pos]
  have IHA : (H : Set G).ncard ≤ K ^ 10 * A.ncard := by
    have : log ((H : Set G).ncard) ≤ log K * 10 + log A.ncard := by
      linarith [(neg_le_abs _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log H_pos).symm
    · rw [exp_add, exp_log A_pos, ← rpow_def_of_pos K_pos]
  -- entropic PFR shows that the entropy of `VA - VH` is small
  have I : log K * (-5) + log A.ncard * (-1/2) + log ((H : Set G).ncard) * (-1/2)
      ≤ - H[VA - VH] := by
    rw [Vindep.rdist_eq VAmeas VHmeas] at this
    linarith
  -- therefore, there exists a point `x₀` which is attained by `VA - VH` with a large probability
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- H[VA - VH]) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _ ((VAmeas.sub VHmeas).comp measurable_id')
  -- massage the previous inequality to get that `A ∩ (H + {x₀})` is large
  have J : K ^ (-5) * A.ncard ^ (1/2) * (H : Set G).ncard ^ (1/2) ≤ (A ∩ (H + {x₀})).ncard := by
    rw [VA'unif.measureReal_preimage_sub VAmeas VH'unif VHmeas Vindep] at h₀
    have := (Real.exp_monotone I).trans h₀
    have hAA'_card : A'.card = A.ncard := by simp [← hAA']
    have hHH'_card : H'.card = (H : Set G).ncard := by simp [← hHH']
    rw [hAA'_card, hHH'_card, le_div_iff₀ (by positivity)] at this
    convert this using 1
    · rw [exp_add, exp_add, ← rpow_def_of_pos K_pos, ← rpow_def_of_pos A_pos,
        ← rpow_def_of_pos H_pos]
      rpow_ring
      norm_num
    · simp [← Set.ncard_coe_finset, hAA', hHH', -add_singleton]
  have Hne : (A ∩ (H + {x₀} : Set G)).Nonempty := by
    have : (0 : ℝ) < (A ∩ (H + {x₀})).ncard := lt_of_lt_of_le (by positivity) J
    simpa [Set.ncard_pos (Set.toFinite _)] using this
  /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  have Z3 :
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ) ≤ (K ^ 6 * A.ncard ^ (1/2 : ℝ) *
        (H : Set G).ncard ^ (-1/2 : ℝ)) * (A ∩ (↑H + {x₀})).ncard := by
    calc
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ)
      _ ≤ Nat.card (A + A) := by
        gcongr; exact Nat.card_mono (toFinite _) <| add_subset_add_left inter_subset_left
      _ ≤ K * A.ncard := hA
      _ = (K ^ 6 * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
          (K ^ (-5 : ℝ) * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (1/2 : ℝ)) := by
        rpow_ring; norm_num
      _ ≤ (K ^ 6 * A.ncard ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
        (A ∩ (↑H + {x₀})).ncard := by gcongr
  obtain ⟨u, huA, hucard, hAu, -⟩ :=
    Set.ruzsa_covering_add (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne (by convert Z3)
  have A_subset_uH : A ⊆ u + H := by
    grw [hAu, inter_subset_right, add_sub_add_comm, singleton_sub_singleton, sub_self]
    simp
  exact ⟨H, u, hucard, IHA, IAH, A_subset_uH⟩

/-- The **polynomial Freiman-Ruzsa (PFR) conjecture**: if $A$ is a subset of an elementary abelian
2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^{11$} cosets of
a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture_improv (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * A.ncard) :
     ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c < 2 * K ^ 11 ∧ (H : Set G).ncard ≤ A.ncard ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < A.ncard ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' (Set.toFinite _) h₀A hA
  -- consider the subgroup `H` given by Lemma `PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ 6 * A.ncard ^ (1/2) * (H : Set G).ncard ^ (-1/2)
      ∧ (H : Set G).ncard ≤ K ^ 10 * A.ncard ∧ A.ncard ≤ K ^ 10 * (H : Set G).ncard
      ∧ A ⊆ c + H :=
    PFR_conjecture_improv_aux h₀A hA
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos; positivity
  rcases le_or_gt ((H : Set G).ncard) A.ncard with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ 6 * A.ncard ^ (1/2) * (H : Set G).ncard ^ (-1/2) := hc
    _ ≤ K ^ 6 * (K ^ 10 * (H : Set G).ncard) ^ (1/2) * (H : Set G).ncard ^ (-1/2) := by
      gcongr
    _ = K ^ 11 := by rpow_ring; norm_num
    _ < 2 * K ^ 11 := by linarith [show 0 < K ^ 11 by positivity]
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / 2 < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : Submodule (ZMod 2) G, (H' : Set G).ncard ≤ A.ncard
          ∧ A.ncard < 2 * (H' : Set G).ncard ∧ H' ≤ H := by
      have A_pos' : 0 < A.ncard := mod_cast A_pos
      exact ZModModule.exists_submodule_subset_card_le Nat.prime_two H h.le A_pos'.ne'
    have : (A.ncard / 2 : ℝ) < (H' : Set G).ncard := by
      rw [div_lt_iff₀ zero_lt_two, mul_comm]; norm_cast
    have H'_pos : (0 : ℝ) < (H' : Set G).ncard := by
      have : 0 < (H' : Set G).ncard := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ :=
      H'.toAddSubgroup.exists_left_transversal_of_le (H := H.toAddSubgroup) H'H
    dsimp at HH'u
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast natCard_add_le
    _ ≤ (K ^ 6 * A.ncard ^ (1 / 2) * ((H : Set G).ncard ^ (-1 / 2)))
          * ((H : Set G).ncard / (H' : Set G).ncard) := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ 6 * A.ncard ^ (1 / 2) * ((H : Set G).ncard ^ (-1 / 2)))
          * ((H : Set G).ncard / (A.ncard / 2)) := by
        gcongr
    _ = (K ^ 6 * A.ncard ^ (1 / 2) * ((H : Set G).ncard ^ (-1 / 2)))
          * ((H : Set G).ncard * (A.ncard :ℝ)⁻¹ * 2) := by
        field_simp
    _ = 2 * (K ^ 6 * A.ncard ^ (1 / 2) * (A.ncard :ℝ)⁻¹ *
          ((H : Set G).ncard ^ (-1 / 2)) * ((H : Set G).ncard)) := by
        ring
    _ = 2 * K ^ 6 * A.ncard ^ (-1/2) * (H : Set G).ncard ^ (1/2) := by
        rpow_ring
        field_simp
        norm_num
    _ ≤ 2 * K ^ 6 * A.ncard ^ (-1/2) * (K ^ 10 * A.ncard) ^ (1/2) := by
        gcongr
    _ = 2 * K ^ 11 := by
        rpow_ring
        norm_num

/-- Corollary of `PFR_conjecture_improv` in which the ambient group is not required to be finite
(but) then $H$ and $c$ are finite. -/
theorem PFR_conjecture_improv' {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (Afin : A.Finite)
    (hA : Nat.card (A + A) ≤ K * A.ncard) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 11 ∧ (H : Set G).ncard ≤ A.ncard ∧ A ⊆ c + H := by
  let G' := Submodule.span (ZMod 2) A
  let G'fin : Fintype G' := (Afin.submoduleSpan _).fintype
  let ι : G'→ₗ[ZMod 2] G := G'.subtype
  have ι_inj : Injective ι := G'.toAddSubgroup.subtype_injective
  let A' : Set G' := ι ⁻¹' A
  have A_rg : A ⊆ range ι := by simp [Submodule.coe_subtype, Subtype.range_coe_subtype, G', ι]
  have cardA' : A'.ncard = A.ncard := Nat.card_preimage_of_injective ι_inj A_rg
  have hA' : Nat.card (A' + A') ≤ K * A'.ncard := by
    rwa [cardA', ← preimage_add _ ι_inj A_rg A_rg,
         Nat.card_preimage_of_injective ι_inj (add_subset_range _ A_rg A_rg)]
  rcases PFR_conjecture_improv (h₀A.preimage' A_rg) hA' with ⟨H', c', hc', hH', hH'₂⟩
  refine ⟨H'.map ι , ι '' c', toFinite _, toFinite (ι '' H'), ?_, ?_, fun x hx ↦ ?_⟩
  · rwa [Nat.card_image_of_injective ι_inj]
  · simpa [Set.ncard_image_of_injective _ ι_inj, ← cardA']
  · erw [← image_add]
    exact ⟨⟨x, Submodule.subset_span hx⟩, hH'₂ hx, rfl⟩

end PFR
