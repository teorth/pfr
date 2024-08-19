import PFR.MoreRuzsaDist

/-!
# The tau functional for multidistance

Definition of the tau functional and basic facts

## Main definitions:


## Main results

-/

open MeasureTheory ProbabilityTheory
universe u

/-- We will frequently be working with finite additive groups with the discrete sigma-algebra. -/
class MeasureableFinGroup (G : Type*)
extends AddCommGroup G, Fintype G,
          MeasurableSpace G, MeasurableSingletonClass G

-- May need an instance lemma here that  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G] follows automatically from [MeasurableFinGroup G]

/-- A structure that packages all the fixed information in the main argument.  See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Problem.20when.20instances.20are.20inside.20a.20structure for more discussion of the design choices here. -/
structure multiRefPackage (G Ω₀ : Type*) [MeasureableFinGroup G] [MeasureSpace Ω₀] where
  (m : ℕ)
  (hm : m ≥ 2)
  (htorsion : ∀ x : G, m • x = 0)
  (hprob : IsProbabilityMeasure (ℙ : Measure Ω₀))
  (X₀ : Ω₀ → G)
  (hmeas : Measurable X₀)
  (η : ℝ)
  (hη : 0 < η)
  (hη': η ≤ 1)


open BigOperators

/-- If $(X_i)_{1 \leq i \leq m}$ is a tuple, we define its $\tau$-functional
$$ \tau[ (X_i)_{1 \leq i \leq m}] := D[(X_i)_{1 \leq i \leq m}] + \eta \sum_{i=1}^m d[X_i; X^0].$$
-/
noncomputable def multiTau {G Ω₀ : Type*} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type*) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) : ℝ :=
  D[X; hΩ] + p.η * ∑ i, d[ X i # p.X₀ ]

-- I can't figure out how to make a τ notation due to the dependent types in the arguments.  But perhaps we don't need one.  Also it may be better to define multiTau in terms of probability measures on G, rather than G-valued random variables, again to avoid dependent type issues.

-- had to force objects to lie in a fixed universe `u` here to avoid a compilation error
/-- A $\tau$-minimizer is a tuple $(X_i)_{1 \leq i \leq m}$ that minimizes the $\tau$-functional among all tuples of $G$-valued random variables. -/
def multiTauMinimizes {G Ω₀ : Type u} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) : Prop := ∀ (Ω' : Fin p.m → Type u) (hΩ' : ∀ i, MeasureSpace (Ω' i)) (X': ∀ i, Ω' i → G), multiTau p Ω hΩ X ≤ multiTau p Ω' hΩ' X'

/-- If $G$ is finite, then a $\tau$ is continuous. -/
lemma multiTau_continuous {G Ω₀ : Type u} [MeasureableFinGroup G] [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) : Continuous
      (fun (μ : Fin p.m → ProbabilityMeasure G) ↦ multiTau p (fun _ ↦ G) (fun i ↦ ⟨ μ i ⟩) (fun _ ↦ id)) := by sorry

/-- If $G$ is finite, then a $\tau$-minimizer exists. -/
lemma multiTau_min_exists {G Ω₀ : Type u} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) : ∃ (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G), multiTauMinimizes p Ω hΩ X := by sorry

/-- If $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, then $\sum_{i=1}^m d[X_i; X^0] \leq \frac{2m}{\eta} d[X^0; X^0]$. -/
lemma multiTau_min_sum_le {G Ω₀ : Type u} [hG: MeasureableFinGroup G] [hΩ₀: MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) (hmin : multiTauMinimizes p Ω hΩ X):
  ∑ i, d[X i # p.X₀] ≤ 2 * p.m * p.η⁻¹ * d[p.X₀ # p.X₀] := by
  have hη : p.η > 0 := p.hη
  have hm : p.m > 0 := by linarith [p.hm]
  have hprob := p.hprob
  calc
    _ = p.η⁻¹ * (0 + p.η * ∑ i, d[X i # p.X₀]) := by
      field_simp
    _ ≤ p.η⁻¹ * (D[X ; hΩ] + p.η * ∑ i, d[X i # p.X₀]) := by
      gcongr
      exact multiDist_nonneg hΩ X
    _ ≤ p.η⁻¹ * (D[fun x ↦ p.X₀ ; fun x ↦ hΩ₀] + p.η * (p.m * d[p.X₀ # p.X₀])) := by
      apply mul_le_mul_of_nonneg_left
      . have ineq := hmin (fun _ ↦ Ω₀) (fun _ ↦ hΩ₀) (fun _ ↦ p.X₀)
        simp [multiTau] at ineq
        exact ineq
      exact inv_nonneg_of_nonneg (le_of_lt hη)
    _ ≤ p.η⁻¹ * (p.m * d[p.X₀ # p.X₀] + 1 * (p.m * d[p.X₀ # p.X₀])) := by
      gcongr
      . apply multidist_ruzsa_III p.hm (fun _ ↦ hΩ₀) (fun _ ↦ p.X₀) _ (Fin.ofNat' 0 hm)
        intro _ _
        simp
        exact ProbabilityTheory.IdentDistrib.refl ( Measurable.aemeasurable p.hmeas)
      . have : 0 ≤ d[p.X₀ # p.X₀] := rdist_nonneg p.hmeas p.hmeas
        positivity
      exact p.hη'
    _ = _ := by
      field_simp
      ring


/-- If  $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, and $k := D[(X_i)_{1 \leq i \leq m}]$, then for any other tuple $(X'_i)_{1 \leq i \leq m}$, one has
  $$ k - D[(X'_i)_{1 \leq i \leq m}] \leq \eta \sum_{i=1}^m d[X_i; X'_i].$$
-/
lemma sub_multiDistance_le {G Ω₀ : Type u} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) (hmin : multiTauMinimizes p Ω hΩ X) (Ω' : Fin p.m → Type u) (hΩ' : ∀ i, MeasureSpace (Ω' i)) (X' : ∀ i, Ω' i → G) : D[X; hΩ] - D[X'; hΩ'] ≤ p.η * ∑ i, d[X i ; (hΩ i).volume # X' i; (hΩ' i).volume ] := by sorry

/-- If  $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, and $k := D[(X_i)_{1 \leq i \leq m}]$, then for any other tuples $(X'_i)_{1 \leq i \leq m}$ and $(Y_i)_{1 \leq i \leq m}$ with the $X'_i$ $G$-valued, one has
  $$ k - D[(X'_i)_{1 \leq i \leq m} | (Y_i)_{1 \leq i \leq m}] \leq \eta \sum_{i=1}^m d[X_i; X'_i|Y_i].$$ -/
lemma sub_condMultiDistance_le {G Ω₀ : Type u} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) (hmin : multiTauMinimizes p Ω hΩ X) (Ω' : Fin p.m → Type u) (hΩ' : ∀ i, MeasureSpace (Ω' i)) (hf: ∀ i, IsFiniteMeasure (hΩ' i).volume) (X' : ∀ i, Ω' i → G) {S : Type u} [MeasurableSpace S] (Y : ∀ i, Ω' i → S) : D[X; hΩ] - D[X'|Y; hΩ'] ≤ p.η * ∑ i, d[X i ; (hΩ i).volume # X' i | Y i; (hΩ' i).volume ] := by sorry

/-- With the notation of the previous lemma, we have
  \begin{equation}\label{5.3-conv}
    k - D[ X'_{[m]} | Y_{[m]} ] \leq \eta \sum_{i=1}^m d[X_{\sigma(i)};X'_i|Y_i]
  \end{equation}
for any permutation $\sigma : \{1,\dots,m\} \rightarrow \{1,\dots,m\}$. -/
lemma sub_condMultiDistance_le'  {G Ω₀ : Type u} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) (hmin : multiTauMinimizes p Ω hΩ X) (Ω' : Fin p.m → Type u) (hΩ' : ∀ i, MeasureSpace (Ω' i)) (hf: ∀ i, IsFiniteMeasure (hΩ' i).volume) (X' : ∀ i, Ω' i → G) {S : Type u} [MeasurableSpace S] (Y : ∀ i, Ω' i → S)  (φ : Equiv.Perm (Fin p.m)) : D[X; hΩ] - D[X'|Y; hΩ'] ≤ p.η * ∑ i, d[X (φ i) ; (hΩ (φ i)).volume # X' i | Y i; (hΩ' i).volume ] := by sorry
