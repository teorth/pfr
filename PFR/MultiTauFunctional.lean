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

variable {Ω₁ Ω₂ Ω'₁ Ω'₂ : Type*} [MeasurableSpace Ω'₁] [MeasurableSpace Ω'₂] {Ω : Fin p.m → Type*}


/-- If $(X_i)_{1 \leq i \leq m}$ is a tuple, we define its $\tau$-functional
$$ \tau[ (X_i)_{1 \leq i \leq m}] := D[(X_i)_{1 \leq i \leq m}] + \eta \sum_{i=1}^m d[X_i; X^0].$$
-/
noncomputable def multiTau (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) : ℝ := sorry

-- TODO: This notation is broken because it can't infer `Ω`
-- @[inherit_doc multiTau]
-- notation3:max "τ[" X " ; " hΩ " | " p"]" => multiTau p X hΩ

/-- A $\tau$-minimizer is a tuple $(X_i)_{1 \leq i \leq m}$ that minimizes the $\tau$-functional among all tuples of $G$-valued random variables. -/
def MultiTauMinimizes (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) : Prop := sorry

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
