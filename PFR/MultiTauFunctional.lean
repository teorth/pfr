import PFR.MoreRuzsaDist

/-!
# The tau functional for multidistance

Definition of the tau functional and basic facts

## Main definitions:


## Main results

-/

open MeasureTheory ProbabilityTheory
universe uG

/-- A structure that packages all the fixed information in the main argument.  -/
structure multiRefPackage :=
  G : Type uG
  hG : AddCommGroup G
  hGf : Fintype G
  hGm : MeasurableSpace G
  hGsc : MeasurableSingletonClass G
  m : ℕ
  htorsion : ∀ x : G, m • x = 0
  Ω₀ : Type*
  hΩ₀ : MeasureSpace Ω₀
  hprob : IsProbabilityMeasure (ℙ : Measure Ω₀)
  X₀ : Ω₀ → G
  hmeas : Measurable X₀
  η : ℝ
  hη : 0 < η

-- May need a lemma here that  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G] follows automatically from the given data

open BigOperators

-- Making the instances inside the multiRefPackage explicit is a hack.  Is there a more elegant way to do this?
/-- If $(X_i)_{1 \leq i \leq m}$ is a tuple, we define its $\tau$-functional
$$ \tau[ (X_i)_{1 \leq i \leq m}] := D[(X_i)_{1 \leq i \leq m}] + \eta \sum_{i=1}^m d[X_i; X^0].$$
-/
noncomputable def multiTau (p : multiRefPackage) (Ω : Fin p.m → Type*) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → p.G) : ℝ :=
  let _ := p.hΩ₀
  let _ := p.hG
  let _ := p.hGm
  D[X; hΩ] + p.η * ∑ i, d[ X i # p.X₀ ]

-- I can't figure out how to make a τ notation due to the dependent types in the arguments.  But perhaps we don't need one.  Also it may be better to define multiTau in terms of probability measures on G, rather than G-valued random variables, again to avoid dependent type issues.

/-- A $\tau$-minimizer is a tuple $(X_i)_{1 \leq i \leq m}$ that minimizes the $\tau$-functional among all tuples of $G$-valued random variables. -/
def multiTauMinimizes (p : multiRefPackage) (Ω : Fin p.m → Type*) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → p.G) : Prop := ∀ (Ω' : Fin p.m → Type*) (hΩ' : ∀ i, MeasureSpace (Ω' i)) (X': ∀ i, Ω' i → p.G), multiTau p Ω hΩ X ≤ multiTau p Ω' hΩ' X'

/-- If $G$ is finite, then a $\tau$-minimizer exists. -/
lemma multiTau_min_exists (p : multiRefPackage) : ∃ (Ω : Fin p.m → Type*) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → p.G), multiTauMinimizes p Ω hΩ X := by sorry

/-- If $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, then $\sum_{i=1}^m d[X_i; X^0] \leq \frac{2m}{\eta} d[X^0; X^0]$. -/
lemma multiTau_min_sum_le (p : multiRefPackage) (Ω : Fin p.m → Type*) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → p.G) (hmin : multiTauMinimizes p Ω hΩ X):
  let _ := p.hΩ₀
  let _ := p.hG
  let _ := p.hGm
  ∑ i, d[X i # p.X₀] ≤ 2 * p.m * p.η⁻¹ * d[p.X₀ # p.X₀] := by sorry

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
