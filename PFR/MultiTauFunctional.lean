import PFR.MoreRuzsaDist

/-!
# The tau functional for multidistance

Definition of the tau functional and basic facts

## Main definitions:


## Main results

-/

open MeasureTheory ProbabilityTheory
universe uG

variable (Ω₀ : Type*) [MeasureSpace Ω₀]
[IsProbabilityMeasure (ℙ : Measure Ω₀)]
variable (G : Type uG) [AddCommGroup G] [Fintype G] [MeasurableSpace G]

/-- A structure that packages all the fixed information in the main argument.  -/
structure multiRefPackage :=
  X₀ : Ω₀ → G
  hmeas : Measurable X₀
  m : ℕ
  η : ℝ
  hη : 0 < η

variable (p : multiRefPackage Ω₀ G)
variable {Ω₀ G}

variable {Ω₁ Ω₂ Ω'₁ Ω'₂ : Type*}


/-- If $(X_i)_{1 \leq i \leq m}$ is a tuple, we define its $\tau$-functional
$$ \tau[ (X_i)_{1 \leq i \leq m}] := D[(X_i)_{1 \leq i \leq m}] + \eta \sum_{i=1}^m d[X_i; X^0].$$
-/
@[pp_dot] noncomputable def multiTau {Ω : Fin p.m → Type*} (hΩ: (i: Fin p.m) ↦ MeasureSpace (Ω i)) (X: (i: Fin p.m) → (Ω i) → G) : ℝ := sorry

@[inherit_doc tau]
notation3:max "τ[" X " ; " hΩ " | " p"]" => multiTau p X hΩ


/-- A $\tau$-minimizer is a tuple $(X_i)_{1 \leq i \leq m}$ that minimizes the $\tau$-functional among all tuples of $G$-valued random variables. -/
def multiTau_minimizes {Ω : Type*} (hΩ: (i: Fin p.m) ↦ MeasureSpace (Ω i)) (X: (i: Fin p.m) → (Ω i) → G) : Prop := sorry

/-- If $G$ is finite, then a $\tau$-minimizer exists. -/
lemma multiTau_min_exists : 0 = 1 := by sorry

/-- If $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, then $\sum_{i=1}^m d[X_i; X^0] \leq \frac{2m}{\eta} d[X^0; X^0]$. -/
lemma multiTau_min_sum_le : 0 = 1 := by sorry

/-- If  $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, and $k := D[(X_i)_{1 \leq i \leq m}]$, then for any other tuple $(X'_i)_{1 \leq i \leq m}$, one has
  $$ k - D[(X'_i)_{1 \leq i \leq m}] \leq \eta \sum_{i=1}^m d[X_i; X'_i].$$
-/
lemma sub_multiDistance_le : 0 = 1 := by sorry

/-- If  $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, and $k := D[(X_i)_{1 \leq i \leq m}]$, then for any other tuples $(X'_i)_{1 \leq i \leq m}$ and $(Y_i)_{1 \leq i \leq m}$ with the $X'_i$ $G$-valued, one has
  $$ k - D[(X'_i)_{1 \leq i \leq m} | (Y_i)_{1 \leq i \leq m}] \leq \eta \sum_{i=1}^m d[X_i; X'_i|Y_i].$$ -/
lemma sub_condMultiDistance_le : 0 = 1 := by sorry

/-- With the notation of the previous lemma, we have
  \begin{equation}\label{5.3-conv}
    k - D[ X'_{[m]} | Y_{[m]} ] \leq \eta \sum_{i=1}^m d[X_{\sigma(i)};X'_i|Y_i]
  \end{equation}
for any permutation $\sigma : \{1,\dots,m\} \rightarrow \{1,\dots,m\}$. -/
lemma sub_condMultiDistance_le' : 0 = 1 := by sorry

open BigOperators

/-- For any $G$-valued random variables $X'_1,X'_2$ and random variables $Z,W$, one can lower
bound $d[X'_1|Z;X'_2|W]$ by
$$k - \eta (d[X^0_1;X'_1|Z] - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2|W] - d[X^0_2;X_2] ).$$
-/
lemma condRuzsaDistance_ge_of_min [MeasurableSingletonClass G]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (h : tau_minimizes p X₁ X₂) (h1 : Measurable X'₁) (h2 : Measurable X'₂)
    (Z : Ω'₁ → S) (W : Ω'₂ → T) (hZ : Measurable Z) (hW : Measurable W) :
    d[X₁ # X₂] - p.η * (d[p.X₀₁ # X'₁ | Z] - d[p.X₀₁ # X₁])
      - p.η * (d[p.X₀₂ # X'₂ | W] - d[p.X₀₂ # X₂]) ≤ d[X'₁ | Z # X'₂ | W] := by
  have hz (a : ℝ) : a = ∑ z in FiniteRange.toFinset Z, (ℙ (Z ⁻¹' {z})).toReal * a := by
    simp_rw [← Finset.sum_mul,← Measure.map_apply hZ (MeasurableSet.singleton _), Finset.sum_toReal_measure_singleton]
    rw [FiniteRange.full hZ]
    simp
  have hw (a : ℝ) : a = ∑ w in FiniteRange.toFinset W, (ℙ (W ⁻¹' {w})).toReal * a := by
    simp_rw [← Finset.sum_mul,← Measure.map_apply hW (MeasurableSet.singleton _), Finset.sum_toReal_measure_singleton]
    rw [FiniteRange.full hW]
    simp
  rw [condRuzsaDist_eq_sum h1 hZ h2 hW, condRuzsaDist'_eq_sum h1 hZ, hz d[X₁ # X₂],
    hz d[p.X₀₁ # X₁], hz (p.η * (d[p.X₀₂ # X'₂ | W] - d[p.X₀₂ # X₂])),
    ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro z _
  rw [condRuzsaDist'_eq_sum h2 hW, hw d[p.X₀₂ # X₂],
    hw ((ℙ (Z ⁻¹' {z})).toReal * d[X₁ # X₂] - p.η * ((ℙ (Z ⁻¹' {z})).toReal *
      d[p.X₀₁ ; ℙ # X'₁ ; ℙ[|Z ← z]] - (ℙ (Z ⁻¹' {z})).toReal * d[p.X₀₁ # X₁])),
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro w _
  rcases eq_or_ne (ℙ (Z ⁻¹' {z})) 0 with hpz | hpz
  . simp [hpz]
  rcases eq_or_ne (ℙ (W ⁻¹' {w})) 0 with hpw | hpw
  . simp [hpw]
  set μ := (hΩ₁.volume)[|Z ← z]
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure ℙ hpz
  set μ' := ℙ[|W ← w]
  have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure ℙ hpw
  suffices d[X₁ # X₂] - p.η * (d[p.X₀₁; volume # X'₁; μ] - d[p.X₀₁ # X₁]) -
    p.η * (d[p.X₀₂; volume # X'₂; μ'] - d[p.X₀₂ # X₂]) ≤ d[X'₁ ; μ # X'₂; μ'] by
    replace this := mul_le_mul_of_nonneg_left this (show 0 ≤ (ℙ (Z ⁻¹' {z})).toReal * (ℙ (W ⁻¹' {w})).toReal by positivity)
    convert this using 1
    ring
  exact distance_ge_of_min' p h h1 h2
