import PFR.Fibring
import PFR.TauFunctional
import PFR.Endgame

/-!
# Improved PFR

An improvement to PFR that lowers the exponent from 12 to 11.

## Main results

*
-/

open MeasureTheory ProbabilityTheory


section GeneralInequality

variable {G : Type*} [AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {Ω₀ : Type*} [MeasureSpace Ω₀]   [IsProbabilityMeasure (ℙ : Measure Ω₀)]

variable (Y : Ω₀ → G) (hY : Measurable Y)

variable (Z₁ Z₂ Z₃ Z₄ : Ω → G)
  (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) (hZ₄ : Measurable Z₄)

variable (h_indep : iIndepFun (fun _i => hG) ![Z₁, Z₂, Z₃, Z₄])

local notation3 "Sum" => Z₁ + Z₂ + Z₃ + Z₄

open scoped BigOperators

lemma ProbabilityTheory.iIndepFun.reindex_four_cadb : iIndepFun (fun _ => hG) ![Z₃, Z₁, Z₄, Z₂] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![2, 0, 3, 1],
    invFun := ![1, 3, 0, 2],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma gen_ineq_aux1 :
    d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] ≤ d[Y # Z₁]
      + (d[Z₁ # Z₂] + d[Z₁ # Z₃] + d[Z₂ # Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 2
      + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₁]) / 4 := by
  have hS : Measurable Sum := ((hZ₁.add' hZ₂).add' hZ₃).add' hZ₄
  have C : d[Z₁ # Z₃] + d[Z₂ # Z₄] = d[Z₁ + Z₂ # Z₃ + Z₄]
           + d[Z₁|Z₁ + Z₂ # Z₃|Z₃ + Z₄] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum] := by
    have M : d[Z₃ # Z₁] + d[Z₄ # Z₂] = d[Z₃ + Z₄ # Z₁ + Z₂]
           + d[Z₃|Z₃ + Z₄ # Z₁|Z₁ + Z₂] + I[Z₃ + Z₁ : Z₁ + Z₂ | Z₃ + Z₁ + Z₄ + Z₂] := by
      apply sum_of_rdist_eq_char_2 ![Z₃, Z₁, Z₄, Z₂] h_indep.reindex_four_cadb (fun i ↦ ?_)
      fin_cases i <;> assumption
    have J1 : Z₃ + Z₁ + Z₄ + Z₂ = Z₁ + Z₂ + Z₃ + Z₄ := by abel
    have J2 : Z₃ + Z₁ = Z₁ + Z₃ := by abel
    rw [J1, J2] at M
    simpa only [rdist_symm (Y := Z₁), rdist_symm (X := Z₄), rdist_symm (X := Z₃ + Z₄),
      condRuzsaDist_symm hZ₃ (hZ₃.add' hZ₄) hZ₁ (hZ₁.add' hZ₂),
      condMutualInfo_comm (hZ₁.add' hZ₃) (hZ₁.add' hZ₂)] using M
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

lemma gen_ineq_aux2 :
    d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃,Sum⟩] ≤ d[Y # Z₁]
      + (d[Z₁ # Z₃] + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]) / 2
      + (H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃] + H[Z₁] - H[Z₃]) / 4 := by
  have hS : Measurable Sum := ((hZ₁.add' hZ₂).add' hZ₃).add' hZ₄
  calc
  d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩]
  = ∑ w, (ℙ (⟨Z₁ + Z₃, Sum⟩ ⁻¹' {w})).toReal * d[Y ; ℙ # Z₁ + Z₂ ; ℙ[|⟨Z₁ + Z₃, Sum⟩ ← w]] := by
    rw [condRuzsaDist'_eq_sum (hZ₁.add' hZ₂) ((hZ₁.add' hZ₃).prod_mk hS)]
  _ ≤ ∑ w, (ℙ (⟨Z₁ + Z₃, Sum⟩ ⁻¹' {w})).toReal * (d[Y ; ℙ # Z₁ ; ℙ[|⟨Z₁ + Z₃, Sum⟩ ← w]]
      + d[Z₁ ; ℙ[|⟨Z₁ + Z₃, Sum⟩ ⁻¹' {w}] # Z₂ ; ℙ[|⟨Z₁ + Z₃, Sum⟩ ⁻¹' {w}]] / 2
      + H[Z₂ | ⟨Z₁ + Z₃, Sum⟩ ← w] / 4 - H[Z₁ | ⟨Z₁ + Z₃, Sum⟩ ← w] / 4) := by sorry
    /- apply Finset.sum_le_sum (fun w h'w ↦ ?_)
    rcases eq_bot_or_bot_lt (ℙ (⟨Z₁ + Z₃, Sum⟩ ⁻¹' {w})) with hw|hw
    · simp [hw]
    gcongr
    have : IsProbabilityMeasure (ℙ[|⟨Z₁ + Z₃, Sum⟩ ← w]) := cond_isProbabilityMeasure ℙ hw.ne'
    have : IndepFun Z₁ Z₂ (ℙ[|⟨Z₁ + Z₃, Sum⟩ ⁻¹' {w}]) := sorry
    have := condRuzsaDist_diff_le' (ℙ : Measure Ω₀) (μ' := ℙ[|⟨Z₁ + Z₃, Sum⟩ ← w]) hY hZ₁ hZ₂ this
    linarith -/
  _ = d[Y # Z₁ | Z₁ + Z₃] + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]/2
      + H[Z₂ | Z₂ + Z₄] / 4 - H[Z₁ | Z₁ + Z₃] / 4 := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_div]
    congr
    · rw [← condRuzsaDist'_eq_sum hZ₁ ((hZ₁.add' hZ₃).prod_mk hS)]
      have : d[Y # Z₁ | ⟨Z₁ + Z₃, Sum⟩] = d[Y # Z₁ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩] := by sorry
      sorry
    · sorry
    · sorry
    · sorry
  _ ≤ (d[Y # Z₁] + d[Z₁ # Z₃]/2 + H[Z₁]/4 - H[Z₃]/4) + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]/2
      + H[Z₂ | Z₂ + Z₄] / 4 - H[Z₁ | Z₁ + Z₃] / 4 := by
    gcongr
    have I : IndepFun Z₁ Z₃ := by exact h_indep.indepFun (show 0 ≠ 2 by decide)
    have := condRuzsaDist_diff_le''' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY hZ₁ hZ₃ I
    linarith
  _ = _ := by ring

/-- Let $Z_1, Z_2, Z_3, Z_4$ be independent $G$-valued random variables, and let $Y$ be another
$G$-valued random variable.  Set $S := Z_1+Z_2+Z_3+Z_4$. Then
$d[Y; Z_1+Z_2|Z_1 + Z_3, S] - d[Y; Z_1]$ is at most
$$ \tfrac{1}{4} (d[Z_1;Z_2] + 2d[Z_1;Z_3] + d[Z_2;Z_4])$$
$$+ \tfrac{1}{4}(d[Z_1|Z_1 + Z_3 ; Z_2|Z_2+Z_4] - d[Z_1|Z_1+Z_2 ; Z_3|Z_3+Z_4]])$$
$$+ \tfrac{1}{8} (\bbH[Z_1+Z_2] - \bbH[Z_3+Z_4] + \bbH[Z_2] - \bbH[Z_3]$$
$$ + \bbH[Z_2|Z_2+Z_4] - \bbH[Z_1|Z_1+Z_3]).$$
-/
lemma gen_ineq : d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] - d[Y # Z₁] ≤
    (d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4
    + (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4
    + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8 := by
  have I1 := gen_ineq_aux1 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep
  have I2 := gen_ineq_aux2 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep
  linarith

end GeneralInequality


section MainEstimates

open MeasureTheory ProbabilityTheory

variable {G : Type*} [AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable {p : refPackage Ω₀₁ Ω₀₂ G}

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {X₁ X₂ X₁' X₂' : Ω → G}
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun (fun _i => hG) ![X₁, X₂, X₂', X₁'])

variable (h_min: tau_minimizes p X₁ X₂)

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

local notation3:max "c[" A " | " B " # " C " | " D "]" => d[p.X₀₁ # A|B] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # C|D] - d[p.X₀₂ # X₂])

section ConstructGood

section aux

variable {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
variable {T₁ T₂ T₃ : Ω' → G} (hT : T₁ + T₂ + T₃ = 0)
variable (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)

local notation3:max "δ[" μ "]" => I[T₁ : T₂ ; μ] + I[T₂ : T₃ ; μ] + I[T₃ : T₁ ; μ]
local notation3:max "δ" => I[T₁ : T₂] + I[T₂ : T₃] + I[T₃ : T₁]

local notation3:max "ψ[" A " # " B "]" => d[A # B] + p.η * (c[A # B])
local notation3:max "ψ[" A "; " μ " # " B " ; " μ' "]" =>
  d[A ; μ # B ; μ'] + p.η * c[A ; μ # B ; μ']

/-- For any $T_1, T_2, T_3$ adding up to $0$, then $k$ is at most
$$ \delta + \eta (d[X^0_1;T_1|T_3]-d[X^0_1;X_1]) + \eta (d[X^0_2;T_2|T_3]-d[X^0_2;X_2])$$
where $\delta = I[T₁ : T₂ ; μ] + I[T₂ : T₃ ; μ] + I[T₃ : T₁ ; μ]$. -/
lemma construct_good_prelim' : k ≤ δ + p.η * c[T₁ | T₃ # T₂ | T₃] := by
  let sum1 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]
  let sum2 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₁; ℙ # T₁; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₁ # X₁]]
  let sum3 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₂; ℙ # T₂; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₂ # X₂]]
  let sum4 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ ψ[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]
  have h2T₃ : T₃ = T₁ + T₂ := by
    calc T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hT, zero_sub]; simp
      _ = T₁ + T₂ := by rw [add_sub_cancel]
  have hP : IsProbabilityMeasure (Measure.map T₃ ℙ) := isProbabilityMeasure_map hT₃.aemeasurable
  -- control sum1 with entropic BSG
  have h1 : sum1 ≤ δ := by
    have h1 : sum1 ≤ 3 * I[T₁ : T₂] + 2 * H[T₃] - H[T₁] - H[T₂] := by
      subst h2T₃; exact ent_bsg hT₁ hT₂
    have h2 : H[⟨T₂, T₃⟩] = H[⟨T₁, T₂⟩]
    · rw [h2T₃, entropy_add_right', entropy_comm] <;> assumption
    have h3 : H[⟨T₁, T₂⟩] = H[⟨T₃, T₁⟩]
    · rw [h2T₃, entropy_add_left, entropy_comm] <;> assumption
    simp_rw [mutualInfo_def] at h1 ⊢; linarith
  -- rewrite sum2 and sum3 as Rusza distances
  have h2 : sum2 = d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁] := by
    simp only [integral_sub (integrable_of_fintype _ _) (integrable_of_fintype _ _), integral_const,
      measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul, sub_left_inj]
    simp_rw [condRuzsaDist'_eq_sum hT₁ hT₃, integral_eq_sum,
      Measure.map_apply hT₃ (measurableSet_singleton _), smul_eq_mul]
  have h3 : sum3 = d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂] := by
    simp only [integral_sub (integrable_of_fintype _ _) (integrable_of_fintype _ _), integral_const,
      measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul, sub_left_inj]
    simp_rw [condRuzsaDist'_eq_sum hT₂ hT₃, integral_eq_sum,
      Measure.map_apply hT₃ (measurableSet_singleton _), smul_eq_mul]
  -- put all these estimates together to bound sum4
  have h4 : sum4 ≤ δ + p.η * ((d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁])
      + (d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂])) := by
    have : sum4 = sum1 + p.η * (sum2 + sum3) := by
      simp only [integral_add (integrable_of_fintype _ _) (integrable_of_fintype _ _),
        integral_mul_left]
    rw [this, h2, h3, add_assoc, mul_add]
    linarith
  have hk : k ≤ sum4 := by
    suffices (Measure.map T₃ ℙ)[fun _ ↦ k] ≤ sum4 by simpa using this
    apply integral_mono_ae (integrable_of_fintype _ _) (integrable_of_fintype _ _)
    apply Countable.ae_of_singleton
    intros t ht
    have : IsProbabilityMeasure (ℙ[|T₃ ⁻¹' {t}]) :=
      cond_isProbabilityMeasure ℙ (by simpa [hT₃] using ht)
    dsimp only
    linarith only [distance_ge_of_min' (μ := ℙ[|T₃ ⁻¹' {t}]) (μ' := ℙ[|T₃ ⁻¹' {t}]) p h_min hT₁ hT₂]
  exact hk.trans h4

open ElementaryAddCommGroup

/-- In fact $k$ is at most
 $$ \delta + \frac{\eta}{6}  \sum_{i=1}^2 \sum_{1 \leq j,l \leq 3; j \neq l}
     (d[X^0_i;T_j|T_l] - d[X^0_i; X_i]).$$
-/
lemma construct_good_improved' : k ≤ δ
    + (p.η / 6) * ((d[p.X₀₁ # T₁ | T₂] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₁ # T₂ | T₁] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₂ | T₃] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₁ # T₃ | T₁] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₃ | T₂] - d[p.X₀₁ # X₁]))
    + (p.η / 6) * ((d[p.X₀₂ # T₁ | T₂] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₁ | T₃] - d[p.X₀₂ # X₂])
                 + (d[p.X₀₂ # T₂ | T₁] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂])
                 + (d[p.X₀₂ # T₃ | T₁] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₃ | T₂] - d[p.X₀₂ # X₂])) :=
    by
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

end aux

open scoped BigOperators

/--   $k$ is at most
$$ \leq I(U : V \, | \, S) + I(V : W \, | \,S) + I(W : U \, | \, S) + \frac{\eta}{6}  \sum_{i=1}^2 \sum_{A,B \in \{U,V,W\}: A \neq B} (d[X^0_i;A|B,S] - d[X^0_i; X_i]).$$
-/
lemma averaged_construct_good : k ≤ I[U : V | S] + I[V : W | S] + I[W : U | S]
    + (p.η / 6) * ((d[p.X₀₁ # U | ⟨V, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # U | ⟨W, S⟩] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₁ # V | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # V | ⟨W, S⟩] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₁ # W | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # W | ⟨V, S⟩] - d[p.X₀₁ # X₁]))
    + (p.η / 6) * ((d[p.X₀₂ # U | ⟨V, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # U | ⟨W, S⟩] - d[p.X₀₂ # X₂])
                 + (d[p.X₀₂ # V | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # V | ⟨W, S⟩] - d[p.X₀₂ # X₂])
                 + (d[p.X₀₂ # W | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # W | ⟨V, S⟩] - d[p.X₀₂ # X₂])) :=
    by
  have hS : Measurable S := ((hX₁.add' hX₂).add' hX₁').add' hX₂'
  have hU : Measurable U := sorry
  have hV : Measurable V := sorry
  have hW : Measurable W := sorry
  have : ∑ x : G, (ℙ (S ⁻¹' {x})).toReal = 1 := sorry
  have Lk : k = ∑ x : G, (ℙ (S ⁻¹' {x})).toReal * k := sorry
  have L1 : d[p.X₀₁ # X₁] = ∑ x : G, (ℙ (S ⁻¹' {x})).toReal * d[p.X₀₁ # X₁] := sorry
  have L2 : d[p.X₀₂ # X₂] = ∑ x : G, (ℙ (S ⁻¹' {x})).toReal * d[p.X₀₂ # X₂] := sorry
  rw [L1, L2, Lk]
  have : U + V + W = 0 := sum_uvw_eq_zero X₁ X₂ X₁'
  simp only [condMutualInfo_eq_sum hS, ← Finset.sum_add_distrib, ← mul_add,
    condRuzsaDist'_prod_eq_sum, hU, hS, hV, hW, ← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum,
    ← mul_assoc (p.η/6), mul_comm (p.η/6), mul_assoc _ _ (p.η/6)]
  apply Finset.sum_le_sum (fun i hi ↦ ?_)
  rcases eq_or_ne (ℙ (S ⁻¹' {i})) 0 with h'i|h'i
  · simp [h'i]
  gcongr





#exit

end ConstructGood

/-- The quantity
$$ \sum_{i=1}^2 \sum_{A,B \in \{U,V,W\}: A \neq B}  d[X_i^0;A|B, S] - d[X_i^0;X_i]$$
is at most $12 k + \frac{4(2 \eta k - I_1)}{1-\eta}$.
-/
proof_wanted dist_diff_bound : 0 = 1

/-- Suppose $0 < \eta < 1/8$.  Let $X_1, X_2$ be tau-minimizers.  Then $d[X_1;X_2] = 0$.
-/
theorem tau_strictly_decreases' : d[X₁ # X₂] = 0 := sorry

end MainEstimates

section EntropicPFR

open MeasureTheory ProbabilityTheory
universe uG

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]

variable {Ω Ω' : Type*} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable {G : Type uG} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G]
  [MeasurableSingletonClass G]
variable (p : refPackage Ω₀₁ Ω₀₂ G) {X₁ : Ω → G} {X₂ : Ω → G} (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)

/-- `entropic_PFR_conjecture_improv`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some
    subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le (2+1/η) d[X^0_1;X^0_2]$. -/
theorem entropic_PFR_conjecture_improv (hpη: p.η = 1/9):
    ∃ H : AddSubgroup G, ∃ Ω : Type uG, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ d[p.X₀₁ # U] + d[p.X₀₂ # U] ≤ (2+1/p.η) * d[p.X₀₁ # p.X₀₂] := sorry

end EntropicPFR


section PFR

open Pointwise Set MeasureTheory ProbabilityTheory

variable {G Ω : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [MeasurableSingletonClass G] {A B : Set G}
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {U V : Ω → G} {K : ℝ}

/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of an elementary abelian
2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^{11}$ cosets of
a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture_improv (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 11 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  sorry

end PFR
