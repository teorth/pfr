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
  have h₂ := second_estimate X₁ X₂ X₁' X₂'
  have h := add_le_add (add_le_add_left h₂ I₁) h₂
  convert h using 1
  field_simp [η]
  ring

local notation3:max "c[" A " # " B "]" => d[p.X₀₁ # A] - d[p.X₀₁ # X₁] + d[p.X₀₂ # B] - d[p.X₀₂ # X₂]

local notation3:max "c[" A " | " B " # " C " | " D "]" => d[p.X₀₁ # A|B] - d[p.X₀₁ # X₁] + d[p.X₀₂ # C|D] - d[p.X₀₂ # X₂]

lemma ruzsa_helper_lemma [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] {A B C : Ω → G}
  (hB : Measurable B) (hC : Measurable C) (hA : Measurable A)
  (H : A = B + C) : d[p.X₀₂ # B | A] = d[p.X₀₂ # C | A] := by
  rw [cond_rdist'_eq_sum, cond_rdist'_eq_sum]
  apply Finset.sum_congr rfl
  intro x
  simp only [Finset.mem_univ, mul_eq_mul_left_iff]
  intro _
  apply Or.intro_left
  sorry
  sorry
  sorry
  sorry
  sorry

lemma Measurable_fun_add  {A B : Ω → G} (hA : Measurable A) (hB : Measurable B) :
  Measurable (A + B) := by
  exact Measurable.add' hA hB

/--
$$ \sum_{i=1}^2 \sum_{A\in\{U,V,W\}} \big(d[X^0_i;A|S] - d[X^0_i;X_i]\big)$$
is less than or equal to
$$ \leq (6 - 3\eta) k + 3(2 \eta k - I_1).$$
-/
lemma sum_dist_diff_le [IsProbabilityMeasure (ℙ : Measure Ω₀₂)] :
  c[U|S # U|S] + c[V|S # V|S]  + c[W|S # W|S] ≤ (6 - 3 * η)*k + 3 * (2*η*k - I₁) := by
  let X₀₁ := p.X₀₁
  let X₀₂ := p.X₀₂
  have ineq1 : d[X₀₁ # U | S] - d[X₀₁ # X₁] ≤ (H[S ; ℙ] - H[X₁ ; ℙ])/2 := by sorry
  have ineq2 : d[X₀₂ # U | S] - d[X₀₂ # X₂] ≤ (H[S ; ℙ] - H[X₂ ; ℙ])/2 := by sorry
  have ineq3 : d[X₀₁ # V | S] - d[X₀₁ # X₁] ≤ (H[S ; ℙ] - H[X₁ ; ℙ])/2 := by sorry
  have ineq4 : d[X₀₂ # V | S] - d[X₀₂ # X₂] ≤ (H[S ; ℙ] - H[X₂ ; ℙ])/2 := by sorry

  let W' := X₂ + X₂'
  have ineq5 : d[X₀₁ # W | S] - d[X₀₁ # X₁] ≤ (H[S ; ℙ] + H[W ; ℙ] - H[X₁ ; ℙ] - H[W' ; ℙ])/2 := by
    sorry

  have ineq6 : d[X₀₂ # W' | S] - d[X₀₂ # X₂] ≤ (H[S ; ℙ] + H[W' ; ℙ] - H[X₂ ; ℙ] - H[W ; ℙ])/2 := by
    sorry

  have dist_eq : d[X₀₂ # W' | S] = d[X₀₂ # W | S]
  · have S_eq : S = (X₂ + X₂') + (X₁' + X₁)
    · rw [add_comm X₁' X₁, add_assoc _ X₂', add_comm X₂', ←add_assoc X₂, ←add_assoc X₂, add_comm X₂]
    apply ruzsa_helper_lemma p (Measurable.add' hX₂ hX₂') (Measurable.add' hX₁' hX₁) _ S_eq
    · rw [S_eq] ; apply (Measurable.add' (Measurable.add' hX₂ hX₂') (Measurable.add' hX₁' hX₁))

  -- Put everything together to bound the sum of the `c` terms
  have ineq7 : c[U|S # U|S] + c[V|S # V|S] + c[W|S # W|S] ≤ 3 * H[S ; ℙ] - 3/2 * H[X₁ ; ℙ] -3/2 * H[X₂ ; ℙ]
  · have step₁ :  c[U|S # U|S] ≤ H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2
    · calc c[U|S # U|S] = (d[p.X₀₁ # U|S] - d[p.X₀₁ # X₁]) + (d[p.X₀₂ # U|S] - d[p.X₀₂ # X₂]) := by ring
        _ ≤ (H[S ; ℙ] - H[X₁ ; ℙ])/2 + (H[S ; ℙ] - H[X₂ ; ℙ])/2 := add_le_add ineq1 ineq2
        _ = H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2 := by ring
    have step₂ : c[V|S # V|S] ≤ H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2
    · calc c[V|S # V|S] =(d[p.X₀₁ # V|S] - d[p.X₀₁ # X₁]) + (d[p.X₀₂ # V|S] - d[p.X₀₂ # X₂]) := by ring
        _ ≤ (H[S ; ℙ] - H[X₁ ; ℙ])/2 + (H[S ; ℙ] - H[X₂ ; ℙ])/2 := add_le_add ineq3 ineq4
        _ = H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2 := by ring
    have step₃ : c[W|S # W|S] ≤  H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2
    · calc c[W|S # W|S] = (d[X₀₁ # W | S] - d[X₀₁ # X₁]) + (d[X₀₂ # W' | S] - d[X₀₂ # X₂]) :=
          by rw [dist_eq] ; ring
        _ ≤ (H[S ; ℙ] + H[W ; ℙ] - H[X₁ ; ℙ] - H[W' ; ℙ])/2 + (H[S ; ℙ] + H[W' ; ℙ] - H[X₂ ; ℙ] - H[W ; ℙ])/2
          := add_le_add ineq5 ineq6
        _ = H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2 := by ring
    calc c[U|S # U|S] + c[V|S # V|S] + c[W|S # W|S] ≤ (H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2) +
      (H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2) + (H[S ; ℙ] - (H[X₁ ; ℙ] + H[X₂ ; ℙ])/2) :=
        add_le_add (add_le_add step₁ step₂) step₃
    _ = 3 * H[S ; ℙ] - 3/2 * H[X₁ ; ℙ] -3/2 * H[X₂ ; ℙ] := by ring

  -- This could maybe be inlined once we've resolved the timeout issue!
  have ineq8 : 3 * H[S ; ℙ] ≤ 3/2 * ( H[X₁ ; ℙ] + H[X₂ ; ℙ]) + 3*(2+η)*k - 3*I₁
  · calc 3 * H[S ; ℙ] ≤ 3 * (1/2 * H[X₁ ; ℙ] + 1/2 * H[X₂ ; ℙ] + (2+η)*k - I₁) := by
          apply (mul_le_mul_left (zero_lt_three' ℝ)).mpr sorry
         -- The following should work `apply ent_ofsum_le p X₁ X₂ X₁' X₂'` but seems to cause a timeout...
      _ =  3/2 * ( H[X₁ ; ℙ] + H[X₂ ; ℙ]) + 3*(2+η)*k - 3*I₁ := by ring

  -- Final computation
  calc c[U|S # U|S] + c[V|S # V|S]  + c[W|S # W|S]  ≤ 3 * H[S ; ℙ] - 3/2 * H[X₁ ; ℙ] -3/2 * H[X₂ ; ℙ] := ineq7
     _ = 3 * H[S ; ℙ] - (3/2 *(H[X₁ ; ℙ] + H[X₂ ; ℙ])) := by ring
     _ ≤ (3/2 * ( H[X₁ ; ℙ] + H[X₂ ; ℙ]) + 3*(2+η)*k - 3*I₁) - (3/2 *(H[X₁ ; ℙ] + H[X₂ ; ℙ])) :=
        sub_le_sub_right ineq8 _
     _ = (6 - 3 * η)*k + 3 * (2*η*k - I₁) := by ring

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
-
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
