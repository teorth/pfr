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

-- May need an instance lemma here that [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G] follows automatically from [MeasurableFinGroup G]

/-- A structure that packages all the fixed information in the main argument. See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Problem.20when.20instances.20are.20inside.20a.20structure for more discussion of the design choices here. -/
structure multiRefPackage (G Ω₀ : Type*) [MeasureableFinGroup G] [MeasureSpace Ω₀] where
  /-- The torsion index of the group we are considering. -/
  (m : ℕ)
  (hm : m ≥ 2)
  (htorsion : ∀ x : G, m • x = 0)
  (hprob : IsProbabilityMeasure (ℙ : Measure Ω₀))
  /-- The random variable -/
  (X₀ : Ω₀ → G)
  (hmeas : Measurable X₀)
  /-- A small constant. The argument will only work for suitably small `η`. -/
  (η : ℝ)
  (hη : 0 < η)
  (hη': η ≤ 1)

/-- If $(X_i)_{1 \leq i \leq m}$ is a tuple, we define its $\tau$-functional
$$ \tau[ (X_i)_{1 \leq i \leq m}] := D[(X_i)_{1 \leq i \leq m}] + \eta \sum_{i=1}^m d[X_i; X^0].$$
-/
noncomputable def multiTau {G Ω₀ : Type*} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type*) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) : ℝ :=
  D[X; hΩ] + p.η * ∑ i, d[ X i # p.X₀ ]

-- I can't figure out how to make a τ notation due to the dependent types in the arguments. But perhaps we don't need one. Also it may be better to define multiTau in terms of probability measures on G, rather than G-valued random variables, again to avoid dependent type issues.

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
    _ ≤ p.η⁻¹ * (D[fun _ ↦ p.X₀ ; fun _ ↦ hΩ₀] + p.η * (p.m * d[p.X₀ # p.X₀])) := by
      apply mul_le_mul_of_nonneg_left
      · have ineq := hmin (fun _ ↦ Ω₀) (fun _ ↦ hΩ₀) (fun _ ↦ p.X₀)
        simp [multiTau] at ineq
        exact ineq
      exact inv_nonneg_of_nonneg (le_of_lt hη)
    _ ≤ p.η⁻¹ * (p.m * d[p.X₀ # p.X₀] + 1 * (p.m * d[p.X₀ # p.X₀])) := by
      gcongr
      · apply multidist_ruzsa_III p.hm (fun _ ↦ hΩ₀) (fun _ ↦ p.X₀) _ (Fin.ofNat' 0 hm)
        intro _ _
        simp
        exact ProbabilityTheory.IdentDistrib.refl ( Measurable.aemeasurable p.hmeas)
      · have : 0 ≤ d[p.X₀ # p.X₀] := rdist_nonneg p.hmeas p.hmeas
        positivity
      exact p.hη'
    _ = _ := by
      field_simp
      ring


/-- If $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, and $k := D[(X_i)_{1 \leq i \leq m}]$, then for any other tuple $(X'_i)_{1 \leq i \leq m}$, one has
  $$ k - D[(X'_i)_{1 \leq i \leq m}] \leq \eta \sum_{i=1}^m d[X_i; X'_i].$$
-/
lemma sub_multiDistance_le {G Ω₀ : Type u} [MeasureableFinGroup G] [hΩ₀: MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (hΩprob: ∀ i, IsProbabilityMeasure (hΩ i).volume) (X : ∀ i, Ω i → G) (hmeasX: ∀ i, Measurable (X i)) (hmin : multiTauMinimizes p Ω hΩ X) (Ω' : Fin p.m → Type u) (hΩ' : ∀ i, MeasureSpace (Ω' i)) (hΩprob': ∀ i, IsProbabilityMeasure (hΩ' i).volume) (X' : ∀ i, Ω' i → G) (hmeasX': ∀ i, Measurable (X' i)) : D[X; hΩ] - D[X'; hΩ'] ≤ p.η * ∑ i, d[X i ; (hΩ i).volume # X' i; (hΩ' i).volume ] := by
  suffices D[X; hΩ] + p.η * ∑ i, d[X i ; (hΩ i).volume # p.X₀; hΩ₀.volume ] ≤ D[X'; hΩ'] + (p.η * ∑ i, d[X i ; (hΩ i).volume # p.X₀; hΩ₀.volume ] + p.η * ∑ i, d[X i ; (hΩ i).volume # X' i; (hΩ' i).volume ]) by
    linarith
  calc
    _ ≤ D[X'; hΩ'] + p.η * ∑ i, d[X' i ; (hΩ' i).volume # p.X₀; hΩ₀.volume ] := hmin Ω' hΩ' X'
    _ ≤ _ := by
      have hη : p.η > 0 := p.hη
      have hprob := p.hprob
      rw [<- mul_add, <-Finset.sum_add_distrib]
      gcongr with i _
      rw [add_comm, rdist_symm (Y := X' i)]
      apply rdist_triangle (hmeasX' i) (hmeasX i) p.hmeas




/-- If $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, and $k := D[(X_i)_{1 \leq i \leq m}]$, then for any other tuples $(X'_i)_{1 \leq i \leq m}$ and $(Y_i)_{1 \leq i \leq m}$ with the $X'_i$ $G$-valued, one has
  $$ k - D[(X'_i)_{1 \leq i \leq m} | (Y_i)_{1 \leq i \leq m}] \leq \eta \sum_{i=1}^m d[X_i; X'_i|Y_i].$$ -/
lemma sub_condMultiDistance_le {G Ω₀ : Type u} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (hΩprob: ∀ i, IsProbabilityMeasure (hΩ i).volume) (X : ∀ i, Ω i → G) (hmeasX: ∀ i, Measurable (X i)) (hmin : multiTauMinimizes p Ω hΩ X) (Ω' : Fin p.m → Type u) (hΩ' : ∀ i, MeasureSpace (Ω' i)) (hΩ'prob: ∀ i, IsProbabilityMeasure (hΩ' i).volume) (X' : ∀ i, Ω' i → G) (hmeasX': ∀ i, Measurable (X' i)) {S : Type u} [Fintype S][MeasurableSpace S] [MeasurableSingletonClass S] (Y : ∀ i, Ω' i → S) (hY : ∀ i, Measurable (Y i)): D[X; hΩ] - D[X'|Y; hΩ'] ≤ p.η * ∑ i, d[X i ; (hΩ i).volume # X' i | Y i; (hΩ' i).volume ] := by
  set μ := fun ω: Fin p.m → S ↦ ∏ i : Fin p.m, (ℙ (Y i ⁻¹' {ω i})).toReal

  have probmes (i : Fin p.m) : ∑ ωi : S, (ℙ (Y i ⁻¹' {ωi})).toReal = 1 := by
    convert Finset.sum_toReal_measure_singleton (s := Finset.univ) (Measure.map (Y i) ℙ) with ω _ i _
    · exact (MeasureTheory.Measure.map_apply (hY i) ( measurableSet_singleton ω)).symm
    replace hΩ'prob := hΩ'prob i
    rw [MeasureTheory.Measure.map_apply (hY i) (Finset.measurableSet _), Finset.coe_univ, Set.preimage_univ, measure_univ, ENNReal.one_toReal]
-- μ has total mass one
  have total : ∑ (ω : Fin p.m → S), μ ω = 1 := calc
    _ = ∏ i, ∑ ωi, (ℙ (Y i ⁻¹' {ωi})).toReal := by
      convert Finset.sum_prod_piFinset Finset.univ _ with ω _ i _
      rfl
    _ = ∏ i, 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact probmes i
    _ = 1 := by
      simp only [Finset.prod_const_one]

  calc
    _ = ∑ (ω: Fin p.m → S), μ ω * D[X; hΩ] - ∑ (ω: Fin p.m → S), μ ω * D[X' ; fun i ↦ MeasureSpace.mk ℙ[|Y i ⁻¹' {ω i}]] := by
      congr
      rw [<-Finset.sum_mul, total, one_mul]
    _ = ∑ (ω: Fin p.m → S), μ ω * (D[X; hΩ] - D[X' ; fun i ↦ MeasureSpace.mk ℙ[|Y i ⁻¹' {ω i}]]) := by
      rw [<-Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro _ _
      exact (mul_sub_left_distrib _ _ _).symm
    _ ≤ ∑ (ω: Fin p.m → S), μ ω * (p.η * ∑ i, d[X i ; (hΩ i).volume # X' i; ℙ[|Y i ⁻¹' {ω i}] ]) := by
      apply Finset.sum_le_sum
      intro ω _
      rcases eq_or_ne (μ ω) 0 with hω | hω
      · simp [hω]
      gcongr
      set hΩ'_cond := fun i ↦ MeasureSpace.mk ℙ[|Y i ⁻¹' {ω i}]
      have hΩ'prob_cond : ∀ i, IsProbabilityMeasure (hΩ'_cond i).volume := by
        intro i
        refine cond_isProbabilityMeasure (hΩ' i).volume ?_
        contrapose! hω
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [hω, ENNReal.zero_toReal]
      exact sub_multiDistance_le p Ω hΩ hΩprob X hmeasX hmin Ω' hΩ'_cond hΩ'prob_cond X' hmeasX'
    _ = p.η * ∑ i, ∑ (ω: Fin p.m → S), μ ω * d[X i ; (hΩ i).volume # X' i; ℙ[|Y i ⁻¹' {ω i}] ] := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      congr with i
      let f := fun j ↦ (fun ωj ↦ (ℙ (Y j ⁻¹' {ωj})).toReal * (if i=j then d[X i ; ℙ # X' i ; ℙ[|Y i ⁻¹' {ωj}]] else 1))
      calc
        _ = ∑ ω : Fin p.m → S, ∏ j, f j (ω j) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.prod_mul_distrib]
          congr
          simp only [Finset.prod_ite_eq, Finset.mem_univ, ↓reduceIte]
        _ = ∏ j, ∑ ωj, f j ωj := Finset.sum_prod_piFinset Finset.univ f
        _ = ∏ j, if i = j then d[X i # X' i | Y i] else 1 := by
          apply Finset.prod_congr rfl
          intro j _
          by_cases hij : i = j
          · simp only [hij, mul_ite, mul_one, ↓reduceIte, f]
            rw [condRuzsaDist'_eq_sum' (hmeasX' i) (hY i), <-hij]
          simp only [mul_ite, mul_one, hij, ↓reduceIte, f]
          exact probmes j
        _ = _ := by
          simp only [Finset.prod_ite_eq, Finset.mem_univ, ↓reduceIte]




/-- With the notation of the previous lemma, we have
  \begin{equation}\label{5.3-conv}
    k - D[ X'_{[m]} | Y_{[m]} ] \leq \eta \sum_{i=1}^m d[X_{\sigma(i)};X'_i|Y_i]
  \end{equation}
for any permutation $\sigma : \{1,\dots,m\} \rightarrow \{1,\dots,m\}$. -/
lemma sub_condMultiDistance_le' {G Ω₀ : Type u} [MeasureableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (hΩprob: ∀ i, IsProbabilityMeasure (hΩ i).volume) (X : ∀ i, Ω i → G) (hmeasX: ∀ i, Measurable (X i)) (hmin : multiTauMinimizes p Ω hΩ X) (Ω' : Fin p.m → Type u) (hΩ' : ∀ i, MeasureSpace (Ω' i)) (hΩ'prob: ∀ i, IsProbabilityMeasure (hΩ' i).volume) (X' : ∀ i, Ω' i → G) (hmeasX': ∀ i, Measurable (X' i)) {S : Type u} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] (Y : ∀ i, Ω' i → S) (hY : ∀ i, Measurable (Y i)) (φ : Equiv.Perm (Fin p.m)) : D[X; hΩ] - D[X'|Y; hΩ'] ≤ p.η * ∑ i, d[X (φ i) ; (hΩ (φ i)).volume # X' i | Y i; (hΩ' i).volume ] := by
  let Xφ := fun i => X (φ i)
  let Ωφ := fun i => Ω (φ i)
  let hΩφ := fun i => hΩ (φ i)
  let hΩφprob := fun i => hΩprob (φ i)
  let hmeasXφ := fun i => hmeasX (φ i)
  calc
    _ = D[Xφ; hΩφ] - D[X'|Y; hΩ'] := by
      congr 1
      rw [multiDist_of_perm hΩ hΩprob X φ]
    _ ≤ _ := by
      apply sub_condMultiDistance_le p Ωφ hΩφ hΩφprob Xφ hmeasXφ _ Ω' hΩ' hΩ'prob X' hmeasX' Y hY
      intro Ω'' hΩ'' X''
      calc
      _ = multiTau p Ω hΩ X := by
        dsimp [multiTau]
        congr 1
        · rw [multiDist_of_perm hΩ hΩprob X φ]
        congr 1
        apply Finset.sum_bijective φ (Equiv.bijective φ)
        · simp only [Finset.mem_univ, implies_true]
        simp only [Finset.mem_univ, imp_self, implies_true]
      _ ≤ multiTau p Ω'' hΩ'' X'' := hmin Ω'' hΩ'' X''
