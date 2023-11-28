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

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]

variable (p : refPackage Ω₀₁ Ω₀₂ G)

variable {Ω : Type*} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable (X₁ X₂ X₁' X₂' : Ω → G)
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun ![hG, hG, hG, hG] ![X₁, X₂, X₁', X₂'])

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
  have h_indep1 : iIndepFun (fun _ ↦ hG) ![X₁, X₂, X₁', X₂'] := by
    convert h_indep using 1
    ext x
    fin_cases x
    all_goals aesop
  have h_indep2 : iIndepFun (fun _ ↦ hG) ![X₁', X₂, X₁, X₂'] := by sorry
  have hident : IdentDistrib (fun a (i : Fin 4) => ![X₁, X₂, X₁', X₂'] i a) (fun a (j : Fin 4) => ![X₁', X₂, X₁, X₂'] j a) := by
    exact { aemeasurable_fst := by sorry
            aemeasurable_snd := sorry
            map_eq := by
              rw [(ProbabilityTheory.iIndepFun_iff_map_prod_eq_prod_map_map (![X₁, X₂, X₁', X₂'])
              (fun _ ↦ hG) (Fin.cases hX₁ <| Fin.cases hX₂ <| Fin.cases hX₁' <|
              Fin.cases hX₂' Fin.rec0)).mp h_indep1,
              (ProbabilityTheory.iIndepFun_iff_map_prod_eq_prod_map_map (![X₁', X₂, X₁, X₂'])
              (fun _ ↦ hG) (Fin.cases hX₁' <| Fin.cases hX₂ <| Fin.cases hX₁ <|
              Fin.cases hX₂' Fin.rec0)).mp h_indep2]
              congr
              ext i
              fin_cases i
              all_goals simp[h₁.map_eq] }
  have hmeas1 : Measurable (fun p : Fin 4 → G => (p 0 + p 1, p 0 + p 1 + p 2 + p 3)) := by measurability
  -- (Mantas)`measurability` hits max heartbeats on my machine on the following lemma
  have hmeas2 : Measurable (fun p : Fin 4 → G => ((p 0 + p 1, p 0 + p 2), p 0 + p 1 + p 2 + p 3)) := sorry
  have hUVS : IdentDistrib (prod U S) (prod V S)
  · convert (IdentDistrib.comp hident hmeas1)
    all_goals {simp; abel}
  have hUVWS : IdentDistrib (prod (prod U W) S) (prod (prod V W) S)
  · convert (IdentDistrib.comp hident hmeas2)
    all_goals {simp; abel}
  rw [condMutualInformation_eq, condMutualInformation_eq, chain_rule'', chain_rule'', chain_rule'',
    chain_rule'', chain_rule'', IdentDistrib.entropy_eq hUVS, IdentDistrib.entropy_eq hUVWS]
  -- (Mantas) only measurability goals left but `measurability` fails again
  all_goals { sorry }

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
  have h₂ := second_estimate X₁ X₂ X₁' X₂'
  have h := add_le_add (add_le_add_left h₂ I₁) h₂
  convert h using 1
  field_simp [η]
  ring

local notation3:max "c[" A " # " B "]" => d[p.X₀₁ # A] - d[p.X₀₁ # X₁] + d[p.X₀₂ # B] - d[p.X₀₂ # X₂]

local notation3:max "c[" A " | " B " # " C " | " D "]" => d[p.X₀₁ # A|B] - d[p.X₀₁ # X₁] + d[p.X₀₂ # C|D] - d[p.X₀₂ # X₂]


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
  exact @sum_add_sum_add_sum_eq_zero G addgroup elem _ _ _

section construct_good

variable (T₁ T₂ T₃ : Ω → G) (hT : T₁+T₂+T₃ = 0)
          (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)

local notation3:max "δ" => I[T₁:T₂] + I[T₂:T₃] + I[T₃:T₁]

local notation3:max "ψ[" A " # " B "]" => d[A # B] + η * (c[A # B])

/-- If $T_1, T_2, T_3$ are $G$-valued random variables with $T_1+T_2+T_3=0$ holds identically and
$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$
Then there exist random variables $T'_1, T'_2$ such that
$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X_1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2]) $$
is at most
$$ \delta + \eta ( d[X^0_1;T_1]-d[X^0_1;X_1]) + \eta (d[X^0_2;T_2]-d[X^0_2;X_2]) $$
$$ + \tfrac12 \eta \bbI[T_1:T_3] + \tfrac12 \eta \bbI[T_2:T_3].$$
-/
lemma construct_good_prelim :
    k ≤ δ + η * c[T₁ # T₂] + η * (I[T₁:T₃] + I[T₂:T₃])/2 := by sorry


/-- If $T_1, T_2, T_3$ are $G$-valued random variables with $T_1+T_2+T_3=0$ holds identically and

$$ \delta := \sum_{1 \leq i < j \leq 3} I[T_i;T_j]$$

Then there exist random variables $T'_1, T'_2$ such that

$$ d[T'_1;T'_2] + \eta (d[X_1^0;T'_1] - d[X_1^0;X _1]) + \eta(d[X_2^0;T'_2] - d[X_2^0;X_2])$$

is at most

$$\delta + \frac{\eta}{3} \biggl( \delta + \sum_{i=1}^2 \sum_{j = 1}^3 (d[X^0_i;T_j] - d[X^0_i; X_i]) \biggr).$$
-/
lemma construct_good :
    k ≤ δ + (η/3) * (δ + c[T₁ # T₁] + c[T₂ # T₂] + c[T₃ # T₃]) := by
  have v1 := construct_good_prelim p X₁ X₂ T₁ T₂ T₃
  have v2 := construct_good_prelim p X₁ X₂ T₁ T₃ T₂
  have v3 := construct_good_prelim p X₁ X₂ T₂ T₁ T₃
  have v4 := construct_good_prelim p X₁ X₂ T₂ T₃ T₁
  have v5 := construct_good_prelim p X₁ X₂ T₃ T₁ T₂
  have v6 := construct_good_prelim p X₁ X₂ T₃ T₂ T₁
  simp only [mutualInformation, entropy_comm hT₂ hT₁, entropy_comm hT₃ hT₁, entropy_comm hT₃ hT₂]
    at *
  linarith
