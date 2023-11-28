import PFR.f2_vec
import PFR.first_estimate
import PFR.second_estimate

/-!
# Endgame

The endgame on tau-minimizers.

Assumptions:

* $X_1, X_2$ are tau-minimizers
* $X_1, X_2, \tilde X_1, \tilde X_2$ be independent random variables, with $X_1,\tilde X_1$ copies of $X_1$ and $X_2,\tilde X_2$ copies of $X_2$.
* $d[X_1;X_2] = k$
* $U := X_1 + X_2$
* $V := \tilde X_1 + X_2$
* $W := X_1 + \tilde X_1$
* $S := X_1 + X_2 + \tilde X_1 + \tilde X_2$.
* $I_1 := I[ U : V | S ]$
* $I_2 := I[ U : W | S ]$
* $I_3 := I[ V : W | S ]$ (not explicitly defined in Lean)

# Main results:

* `sum_condMutual_le` : An upper bound on the total conditional mutual information $I_1+I_2+I_3$.
* `sum_dist_diff_le`: A sum of the "costs" of $U$, $V$, $W$.
* `construct_good`: A construction of two random variables with small Ruzsa distance between them given some random variables with control on total cost, as well as total mutual information.
-/

universe u

open MeasureTheory ProbabilityTheory

variable {G : Type u} [addgroup: AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [elem: ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

variable {Ω₀₁ Ω₀₂ : Type u} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type u} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun (fun _i => hG) ![X₁, X₂, X₁', X₂'])

variable (h_min: tau_minimizes p X₁ X₂)

/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[ X₁ # X₂]

/-- `U := X₁ + X₂` -/
local notation3 "U" => X₁ + X₂

/-- `V := X₁' + X₂` -/
local notation3 "V" => X₁' + X₂

/-- `W := X₁' + X₁` -/
local notation3 "W" => X₁' + X₁

/-- `S := X₁ + X₂ + X₁' + X₂'` -/
local notation3 "S" => X₁ + X₂ + X₁' + X₂'

/-- `I₁ := I[ U : V | S ]`, the conditional mutual information of `U = X₁ + X₂` and `V = X₁' + X₂`
given the quadruple sum `S = X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => I[ U : V | S ]

/-- `I₂ := I[ U : W | S ]`, the conditional mutual information of `U = X₁ + X₂` and `W = X₁' + X₁`
given the quadruple sum `S = X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₂" => I[ U : W | S ]

/-- The quantity $I_3 = I[V:W|S]$ is equal to $I_2$. -/
lemma I₃_eq : I[ V : W | S ] = I₂ := by
  -- Note(kmill): I'm not sure this is going anywhere, but in case some of this reindexing
  -- is useful, and this setting-up of the `I'` function, here it is.
  -- Swap X₁ and X₁'
  let perm : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3
  have hp : ![X₁, X₁', X₂, X₂'] = ![X₁', X₁, X₂, X₂'] ∘ perm := by
    ext i
    fin_cases i <;> rfl
  let I' (Xs : Fin 4 → Ω → G) := I[Xs 0 + Xs 2 : Xs 1 + Xs 0 | Xs 0 + Xs 2 + Xs 1 + Xs 3]
  have hI₂ : I₂ = I' ![X₁, X₁', X₂, X₂'] := rfl
  have hI₃ : I[V : W | S] = I' ![X₁', X₁, X₂, X₂'] := by
    rw [add_comm X₁' X₁]
    congr 1
    change _ = X₁' + X₂ + X₁ + X₂'
    simp [add_assoc, add_left_comm]
  rw [hI₂, hI₃, hp]
  -- ⊢ I' ![X₁', X₁, X₂, X₂'] = I' (![X₁', X₁, X₂, X₂'] ∘ perm)
  sorry

/--
$$ I(U : V | S) + I(V : W | S) + I(W : U | S) $$
is less than or equal to
$$ 6 \eta k - \frac{1 - 5 \eta}{1-\eta} (2 \eta k - I_1).$$
-/
lemma sum_condMutual_le :
    I[ U : V | S ] + I[ V : W | S ] + I[ W : U | S ]
      ≤ 6 * η * k - (1 - 5 * η) / (1 - η) * (2 * η * k - I₁) := by
  have : I[W:U|S] = I₂ := by
    rw [condMutualInformation_comm]
    · exact Measurable.add' hX₁' hX₁
    · exact Measurable.add' hX₁ hX₂
  rw [I₃_eq, this]
  have h₂ := second_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
  have h := add_le_add (add_le_add_left h₂ I₁) h₂
  convert h using 1
  field_simp [η]
  ring

local notation3:max "c[" A "; " μ " # " B " ; " μ' "]" =>
  d[p.X₀₁; ℙ # A; μ] - d[p.X₀₁ # X₁] + (d[p.X₀₂; ℙ # B; μ'] - d[p.X₀₂ # X₂])

local notation3:max "c[" A " # " B "]" =>
  d[p.X₀₁ # A] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # B] - d[p.X₀₂ # X₂])

local notation3:max "c[" A " | " B " # " C " | " D "]" =>
  d[p.X₀₁ # A|B] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # C|D] - d[p.X₀₂ # X₂])


/--
$$ \sum_{i=1}^2 \sum_{A\in\{U,V,W\}} \big(d[X^0_i;A|S] - d[X^0_i;X_i]\big)$$
is less than or equal to
$$ \leq (6 - 3\eta) k + 3(2 \eta k - I_1).$$
-/
lemma sum_dist_diff_le : c[U|S # U|S] + c[V|S # V|S]  + c[W|S # W|S] ≤ (6 - 3 * η)*k + 3 * (2*η*k - I₁) := by sorry

/-- $U+V+W=0$. -/
lemma sum_uvw_eq_zero : U+V+W = 0 := by
  funext ω
  dsimp
  rw [add_comm (X₁' ω) (X₂ ω)]
  exact @ElementaryAddCommGroup.sum_add_sum_add_sum_eq_zero G addgroup elem _ _ _

section construct_good

variable {T₁ T₂ T₃ : Ω → G} (hT : T₁+T₂+T₃ = 0)
          (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)

local notation3:max "δ" => I[T₁:T₂] + I[T₂:T₃] + I[T₃:T₁]

local notation3:max "ψ[" A " # " B "]" => d[A # B] + η * c[A # B]

local notation3:max "ψ[" A "; " μ " # " B " ; " μ' "]" =>
  d[A ; μ # B ; μ'] + η * c[A ; μ # B ; μ']

open BigOperators in
/-- If $T_1, T_2, T_3$ are $G$-valued random variables with $T_1+T_2+T_3=0$ holds identically and
$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$
Then there exist random variables $T'_1, T'_2$ such that
$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X_1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2]) $$
is at most
$$ \delta + \eta ( d[X^0_1;T_1]-d[X^0_1;X_1]) + \eta (d[X^0_2;T_2]-d[X^0_2;X_2]) $$
$$ + \tfrac12 \eta I[T_1:T_3] + \tfrac12 \eta I[T_2:T_3].$$
-/
lemma construct_good_prelim :
    k ≤ δ + η * c[T₁ # T₂] + η * (I[T₁:T₃] + I[T₂:T₃])/2 := by
  let sum1 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]
  let sum2 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₁; ℙ # T₁; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₁ # X₁]]
  let sum3 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₂; ℙ # T₂; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₂ # X₂]]
  let sum4 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ ψ[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]

  have hη : 0 ≤ η := by norm_num [η]
  have hP : IsProbabilityMeasure (Measure.map T₃ ℙ) := isProbabilityMeasure_map hT₃.aemeasurable
  have h2T₃ : T₃ = T₁ + T₂
  · calc T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hT, zero_sub]; ext x; simp
      _ = T₁ + T₂ := by rw [add_sub_cancel]
  have h2T₁ : T₁ = T₂ + T₃ := by ext; simp [h2T₃, add_left_comm]
  have h2T₂ : T₂ = T₃ + T₁ := by ext; simp [h2T₁, add_left_comm]

  have h1 : sum1 ≤ δ
  · have h1 : sum1 ≤ 3 * I[T₁ : T₂] + 2 * H[T₃] - H[T₁] - H[T₂] := ent_bsg hT₁ hT₂ h2T₃
    have h2 : H[⟨T₂, T₃⟩] = H[⟨T₁, T₂⟩]
    · apply entropy_of_comp_eq_of_comp ℙ (hT₂.prod_mk hT₃) (hT₁.prod_mk hT₂)
        (fun x ↦ (x.1 + x.2, x.1)) (fun x ↦ (x.2, x.1 + x.2))
      · ext1 x; simp [h2T₁]
      · ext1 x; simp [h2T₃]
    have h3 : H[⟨T₁, T₂⟩] = H[⟨T₃, T₁⟩]
    · apply entropy_of_comp_eq_of_comp ℙ (hT₁.prod_mk hT₂) (hT₃.prod_mk hT₁)
        (fun x ↦ (x.1 + x.2, x.1)) (fun x ↦ (x.2, x.1 + x.2))
      · ext1 x; simp [h2T₃]
      · ext1 x; simp [h2T₂]
    simp_rw [mutualInformation_def] at h1 ⊢; linarith

  have h2 : η * sum2 ≤ η * (d[p.X₀₁ # T₁] - d[p.X₀₁ # X₁] + I[T₁ : T₃] / 2)
  · have : sum2 = d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁]
    · simp [integral_sub (integrable_of_fintype _ _) (integrable_of_fintype _ _)]
      simp_rw [cond_rdist'_eq_sum hT₁ hT₃, integral_eq_sum,
        Measure.map_apply hT₃ (measurableSet_singleton _), smul_eq_mul]
    gcongr
    linarith [condDist_le' ℙ ℙ p.hmeas1 hT₁ hT₃]

  have h3 : η * sum3 ≤ η * (d[p.X₀₂ # T₂] - d[p.X₀₂ # X₂] + I[T₂ : T₃] / 2)
  · have : sum3 = d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂]
    · simp [integral_sub (integrable_of_fintype _ _) (integrable_of_fintype _ _)]
      simp_rw [cond_rdist'_eq_sum hT₂ hT₃, integral_eq_sum,
        Measure.map_apply hT₃ (measurableSet_singleton _), smul_eq_mul]
    gcongr
    linarith [condDist_le' ℙ ℙ p.hmeas2 hT₂ hT₃]

  have h4 : sum4 ≤ δ + η * c[T₁ # T₂] + η * (I[T₁ : T₃] + I[T₂ : T₃]) / 2
  · have : sum4 = sum1 + η * (sum2 + sum3)
    · simp only [integral_add (integrable_of_fintype _ _) (integrable_of_fintype _ _),
        integral_mul_left]
    linarith

  have hk : k ≤ sum4
  · suffices (Measure.map T₃ ℙ)[fun _ ↦ k] ≤ sum4 by simpa using this
    apply integral_mono_ae (integrable_of_fintype _ _) (integrable_of_fintype _ _)
    apply Countable.ae_of_singleton
    intros t ht
    have : IsProbabilityMeasure (ℙ[|T₃ ⁻¹' {t}]) :=
      cond_isProbabilityMeasure ℙ (by simpa [hT₃] using ht)
    dsimp only
    linarith only [distance_ge_of_min' (μ := ℙ[|T₃ ⁻¹' {t}]) (μ' := ℙ[|T₃ ⁻¹' {t}]) p h_min hT₁ hT₂]
  exact hk.trans h4

  -- have h7 : k ≤ ψ[Y₁ # Y₂] := sorry

/-- If $T_1, T_2, T_3$ are $G$-valued random variables with $T_1+T_2+T_3=0$ holds identically and

$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$

Then there exist random variables $T'_1, T'_2$ such that

$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X _1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2])$$

is at most

$$\delta + \frac{\eta}{3} \biggl( \delta + \sum_{i=1}^2 \sum_{j = 1}^3 (d[X^0_i;T_j] - d[X^0_i; X_i]) \biggr).$$
-/
lemma construct_good :
    k ≤ δ + (η/3) * (δ + c[T₁ # T₁] + c[T₂ # T₂] + c[T₃ # T₃]) := by
  have v1 := construct_good_prelim p X₁ X₂ h_min hT hT₁ hT₂ hT₃
  have v2 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₁ hT₃ hT₂
  have v3 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₂ hT₁ hT₃
  have v4 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₂ hT₃ hT₁
  have v5 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₃ hT₁ hT₂
  have v6 := construct_good_prelim p X₁ X₂ h_min (by rw [← hT]; abel) hT₃ hT₂ hT₁
  simp only [mutualInformation, entropy_comm hT₂ hT₁, entropy_comm hT₃ hT₁, entropy_comm hT₃ hT₂]
    at *
  linarith
