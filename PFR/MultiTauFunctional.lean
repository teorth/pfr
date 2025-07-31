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
class MeasurableFinGroup (G : Type*)
extends AddCommGroup G, Fintype G,
          MeasurableSpace G, MeasurableSingletonClass G

-- May need an instance lemma here that [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G] follows automatically from [MeasurableFinGroup G]

/-- A structure that packages all the fixed information in the main argument. See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Problem.20when.20instances.20are.20inside.20a.20structure for more discussion of the design choices here. -/
structure multiRefPackage (G Ω₀ : Type u) [MeasurableFinGroup G] [MeasureSpace Ω₀] where
  /-- The torsion index of the group we are considering. -/
  m : ℕ
  hm : m ≥ 2
  htorsion : ∀ x : G, m • x = 0
  hprob : IsProbabilityMeasure (ℙ : Measure Ω₀)
  /-- The random variable -/
  X₀ : Ω₀ → G
  hmeas : Measurable X₀
  /-- A small constant. The argument will only work for suitably small `η`. -/
  η : ℝ
  hη : 0 < η
  hη' : η ≤ 1

/-- If $(X_i)_{1 \leq i \leq m}$ is a tuple, we define its $\tau$-functional
$$ \tau[ (X_i)_{1 \leq i \leq m}] := D[(X_i)_{1 \leq i \leq m}] + \eta \sum_{i=1}^m d[X_i; X^0].$$
-/
noncomputable def multiTau {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type*) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G) : ℝ :=
  D[X; hΩ] + p.η * ∑ i, d[ X i # p.X₀ ]

-- I can't figure out how to make a τ notation due to the dependent types in the arguments. But perhaps we don't need one. Also it may be better to define multiTau in terms of probability measures on G, rather than G-valued random variables, again to avoid dependent type issues.

lemma multiTau_of_ident {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀]
    (p : multiRefPackage G Ω₀)
    {Ω₁ Ω₂ : Fin p.m → Type*} (hΩ₁ : ∀ i, MeasureSpace (Ω₁ i)) (hΩ₂ : ∀ i, MeasureSpace (Ω₂ i))
    {X₁ : ∀ i, Ω₁ i → G} {X₂ : ∀ i, Ω₂ i → G} (h_ident : ∀ i, IdentDistrib (X₁ i) (X₂ i)) :
    multiTau p Ω₁ hΩ₁ X₁ = multiTau p Ω₂ hΩ₂ X₂ := by
  unfold multiTau; congr 1
  . exact multiDist_copy _ _ _ _ h_ident
  congr 2 with i
  have := p.hmeas
  exact IdentDistrib.rdist_congr_left (by fun_prop) (h_ident i)

-- had to force objects to lie in a fixed universe `u` here to avoid a compilation error
/-- A $\tau$-minimizer is a tuple $(X_i)_{1 \leq i \leq m}$ that minimizes the $\tau$-functional among all tuples of $G$-valued random variables. -/
def multiTauMinimizes {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀]
    (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i))
    (X : ∀ i, Ω i → G) : Prop :=
  ∀ (Ω' : Fin p.m → Type u) (hΩ' : ∀ i, MeasureSpace (Ω' i))
    (_hP : ∀ i, IsProbabilityMeasure (volume : Measure (Ω' i)))(X' : ∀ i, Ω' i → G)
    (_hX' : ∀ i, Measurable (X' i)),
  multiTau p Ω hΩ X ≤ multiTau p Ω' hΩ' X'

lemma multiTauMinimizes_of_ident {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀]
    (p : multiRefPackage G Ω₀) {Ω₁ Ω₂ : Fin p.m → Type u}
    (hΩ₁ : ∀ i, MeasureSpace (Ω₁ i)) (hΩ₂ : ∀ i, MeasureSpace (Ω₂ i))
    {X₁ : ∀ i, Ω₁ i → G} {X₂ : ∀ i, Ω₂ i → G}
    (h_ident : ∀ i, IdentDistrib (X₁ i) (X₂ i)) (hmin : multiTauMinimizes p Ω₁ hΩ₁ X₁) :
    multiTauMinimizes p Ω₂ hΩ₂ X₂ := by
  intro Ω' hΩ' hprob X' hX'
  convert hmin Ω' hΩ' hprob X' hX' using 1
  apply multiTau_of_ident _ _ _ (fun i ↦ (h_ident i).symm)

/-- If $G$ is finite, then $\tau$ is continuous. -/
lemma multiTau_continuous {G Ω₀ : Type u} [MeasurableFinGroup G] [TopologicalSpace G]
    [DiscreteTopology G] [BorelSpace G] [MeasureSpace Ω₀] (p : multiRefPackage G Ω₀) :
    Continuous (fun (μ : Fin p.m → ProbabilityMeasure G) ↦
      multiTau p (fun _ ↦ G) (fun i ↦ ⟨μ i⟩) (fun _ ↦ id)) := by
  simp only [multiTau, multiDist, Measure.map_id]
  apply Continuous.add (Continuous.sub ?_ ?_) ?_
  · simp [entropy]
    let f : (Fin p.m → G) → G := fun x ↦ ∑ i, x i
    have fcont : Continuous f := by fun_prop
    change Continuous fun (x : Fin p.m → ProbabilityMeasure G) ↦
      Hm[(ProbabilityMeasure.map (ProbabilityMeasure.pi x) fcont.aemeasurable : Measure G)]
    apply continuous_measureEntropy_probabilityMeasure.comp
    exact (ProbabilityMeasure.continuous_map fcont).comp ProbabilityMeasure.continuous_pi
  · apply Continuous.mul continuous_const
    refine continuous_finset_sum Finset.univ ?_
    intro i hi
    apply continuous_entropy_restrict_probabilityMeasure.comp
    exact continuous_apply i
  · apply Continuous.mul continuous_const
    refine continuous_finset_sum Finset.univ ?_
    intro i hi
    have := p.hprob
    apply (continuous_rdist_restrict_probabilityMeasure₁_left p.X₀ volume p.hmeas).comp
    exact continuous_apply i

/-- If $G$ is finite, then a $\tau$-minimizer exists. -/
lemma multiTau_min_exists_measure {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀]
    (p : multiRefPackage G Ω₀) :
    ∃ (μ : Fin p.m → Measure G), (∀ i, IsProbabilityMeasure (μ i)) ∧
    ∀ (ν : Fin p.m → Measure G), (∀ i, IsProbabilityMeasure (ν i)) →
    multiTau p (fun _ ↦ G) (fun i ↦ ⟨μ i⟩) (fun _ ↦ id) ≤
      multiTau p (fun _ ↦ G) (fun i ↦ ⟨ν i⟩) (fun _ ↦ id) := by
  let _i : TopologicalSpace G := (⊥ : TopologicalSpace G) -- Equip G with the discrete topology.
  have : DiscreteTopology G := ⟨rfl⟩
  let T : (Π (i : Fin p.m), ProbabilityMeasure G) → ℝ := -- restrict τ to the compact subspace
    fun μ ↦ multiTau p (fun _ ↦ G) (fun i ↦ ⟨μ i⟩) (fun _ ↦ id)
  have T_cont : Continuous T := multiTau_continuous p
  have : Inhabited G := ⟨0⟩ -- Need to record this for Lean to know that proba measures exist.
  obtain ⟨μ, _, hμ⟩ := IsCompact.exists_isMinOn isCompact_univ (by simp) T_cont.continuousOn
  refine ⟨fun i ↦ μ i, fun i ↦ by infer_instance, fun ν hν ↦ ?_⟩
  rw [isMinOn_univ_iff] at hμ
  let ν' : Fin p.m → ProbabilityMeasure G := fun i ↦ ⟨ν i, hν i⟩
  exact hμ ν'


/-- If $G$ is finite, then a $\tau$-minimizer exists. -/
lemma multiTau_min_exists {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀]
    (p : multiRefPackage G Ω₀) :
    ∃ (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i)) (X : ∀ i, Ω i → G),
    (∀ i, Measurable (X i)) ∧ (∀ i, IsProbabilityMeasure (hΩ i).volume)
    ∧ multiTauMinimizes p Ω hΩ X := by
  let μ := (multiTau_min_exists_measure p).choose
  refine ⟨fun i ↦ G, fun i ↦ ⟨μ i⟩, fun i ↦ id, fun i ↦ measurable_id,
    (multiTau_min_exists_measure p).choose_spec.1, ?_⟩
  intro Ω' ν hν X hX
  have : multiTau p (fun i ↦ G) (fun i ↦ ⟨(volume : Measure (Ω' i)).map (X i)⟩) (fun i ↦ id) =
      multiTau p Ω' ν X := by
    apply multiTau_of_ident _ _ _ (fun i ↦ ?_)
    apply identDistrib_map (hX i) measurable_id
  rw [← this]
  apply (multiTau_min_exists_measure p).choose_spec.2
  intro i
  apply isProbabilityMeasure_map
  exact (hX i).aemeasurable

/-- If $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, then $\sum_{i=1}^m d[X_i; X^0] \leq \frac{2m}{\eta} d[X^0; X^0]$. -/
lemma multiTau_min_sum_le {G Ω₀ : Type u} [hG : MeasurableFinGroup G] [hΩ₀ : MeasureSpace Ω₀]
    (p : multiRefPackage G Ω₀) (Ω : Fin p.m → Type u) (hΩ : ∀ i, MeasureSpace (Ω i))
    (hprobΩ : ∀ i, IsProbabilityMeasure (ℙ : Measure (Ω i))) (X : ∀ i, Ω i → G)
    (hX : ∀ i, Measurable (X i)) (h_min : multiTauMinimizes p Ω hΩ X):
  ∑ i, d[X i # p.X₀] ≤ 2 * p.m * p.η⁻¹ * d[p.X₀ # p.X₀] := by
  have hη : p.η > 0 := p.hη
  have hm : p.m > 0 := by linarith [p.hm]
  have hprob := p.hprob
  calc
    _ = p.η⁻¹ * (0 + p.η * ∑ i, d[X i # p.X₀]) := by
      field_simp
    _ ≤ p.η⁻¹ * (D[X ; hΩ] + p.η * ∑ i, d[X i # p.X₀]) := by
      gcongr
      exact multiDist_nonneg hΩ hprobΩ X hX
    _ ≤ p.η⁻¹ * (D[fun _ ↦ p.X₀ ; fun _ ↦ hΩ₀] + p.η * (p.m * d[p.X₀ # p.X₀])) := by
      apply mul_le_mul_of_nonneg_left
      · have ineq := h_min (fun _ ↦ Ω₀) (fun _ ↦ hΩ₀) (fun _ ↦ hprob) (fun _ ↦ p.X₀)
          (fun _ ↦ p.hmeas)
        simp only [multiTau, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul] at ineq
        exact ineq
      exact inv_nonneg_of_nonneg (le_of_lt hη)
    _ ≤ p.η⁻¹ * (p.m * d[p.X₀ # p.X₀] + 1 * (p.m * d[p.X₀ # p.X₀])) := by
      gcongr
      · have : NeZero p.m := ⟨hm.ne'⟩
        apply multidist_ruzsa_III p.hm (fun _ ↦ hΩ₀) (fun _ ↦ p.X₀) _ (fun _ ↦ p.hmeas)
          (fun _ ↦ p.hprob) _ 0
        . intro _ _
          simp
          exact .refl p.hmeas.aemeasurable
        intro _; infer_instance
      · have : 0 ≤ d[p.X₀ # p.X₀] := rdist_nonneg p.hmeas p.hmeas
        positivity
      exact p.hη'
    _ = _ := by
      field_simp
      ring


/-- If $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, and $k := D[(X_i)_{1 \leq i \leq m}]$, then for any other tuple $(X'_i)_{1 \leq i \leq m}$, one has
  $$ k - D[(X'_i)_{1 \leq i \leq m}] \leq \eta \sum_{i=1}^m d[X_i; X'_i].$$
-/
lemma sub_multiDistance_le {G Ω₀ : Type u} [MeasurableFinGroup G] [hΩ₀: MeasureSpace Ω₀]
    {p : multiRefPackage G Ω₀} {Ω : Fin p.m → Type u} {hΩ : ∀ i, MeasureSpace (Ω i)}
    (hΩprob : ∀ i, IsProbabilityMeasure (hΩ i).volume) {X : ∀ i, Ω i → G}
    (hmeasX : ∀ i, Measurable (X i)) (h_min : multiTauMinimizes p Ω hΩ X)
    {Ω' : Fin p.m → Type u} {hΩ' : ∀ i, MeasureSpace (Ω' i)}
    (hΩprob' : ∀ i, IsProbabilityMeasure (hΩ' i).volume)
    {X' : ∀ i, Ω' i → G} (hmeasX' : ∀ i, Measurable (X' i)) :
    D[X; hΩ] - D[X'; hΩ'] ≤ p.η * ∑ i, d[X i ; (hΩ i).volume # X' i; (hΩ' i).volume ] := by
  suffices D[X; hΩ] + p.η * ∑ i, d[X i ; (hΩ i).volume # p.X₀; hΩ₀.volume ]
      ≤ D[X'; hΩ'] + (p.η * ∑ i, d[X i ; (hΩ i).volume # p.X₀; hΩ₀.volume ]
        + p.η * ∑ i, d[X i ; (hΩ i).volume # X' i; (hΩ' i).volume ]) by linarith
  calc
    _ ≤ D[X'; hΩ'] + p.η * ∑ i, d[X' i ; (hΩ' i).volume # p.X₀; hΩ₀.volume ] :=
      h_min Ω' hΩ' hΩprob' X' hmeasX'
    _ ≤ _ := by
      have hη : p.η > 0 := p.hη
      have hprob := p.hprob
      rw [←  mul_add, ← Finset.sum_add_distrib]
      gcongr with i _
      rw [add_comm, rdist_symm (Y := X' i)]
      apply rdist_triangle (hmeasX' i) (hmeasX i) p.hmeas

lemma sub_multiDistance_le' {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀]
    {p : multiRefPackage G Ω₀} {Ω : Fin p.m → Type u} {hΩ : ∀ i, MeasureSpace (Ω i)}
    (hΩprob : ∀ i, IsProbabilityMeasure (hΩ i).volume)
    {X : ∀ i, Ω i → G} (hmeasX : ∀ i, Measurable (X i)) (h_min : multiTauMinimizes p Ω hΩ X)
    {Ω' : Fin p.m → Type u} {hΩ' : ∀ i, MeasureSpace (Ω' i)}
    (hΩ'prob: ∀ i, IsProbabilityMeasure (hΩ' i).volume) {X' : ∀ i, Ω' i → G}
    (hmeasX': ∀ i, Measurable (X' i)) (φ : Equiv.Perm (Fin p.m)) :
    D[X; hΩ] - D[X'; hΩ'] ≤
      p.η * ∑ i, d[X (φ i) ; (hΩ (φ i)).volume # X' i; (hΩ' i).volume ] := by
  let Xφ := fun i => X (φ i)
  let Ωφ := fun i => Ω (φ i)
  let hΩφ := fun i => hΩ (φ i)
  let hΩφprob := fun i => hΩprob (φ i)
  let hmeasXφ := fun i => hmeasX (φ i)
  calc
    _ = D[Xφ; hΩφ] - D[X'; hΩ'] := by
      congr 1
      rw [multiDist_of_perm hΩ hΩprob X φ]
    _ ≤ _ := by
      apply sub_multiDistance_le hΩφprob hmeasXφ _ hΩ'prob hmeasX'
      intro Ω'' hΩ'' hprob X'' hX''
      calc
      _ = multiTau p Ω hΩ X := by
        dsimp [multiTau]
        congr 1
        · exact multiDist_of_perm hΩ hΩprob X φ
        congr 1
        exact Fintype.sum_equiv φ _ _ fun _ ↦ rfl
      _ ≤ multiTau p Ω'' hΩ'' X'' := h_min Ω'' hΩ'' hprob X'' hX''

/-- If $(X_i)_{1 \leq i \leq m}$ is a $\tau$-minimizer, and $k := D[(X_i)_{1 \leq i \leq m}]$, then for any other tuples $(X'_i)_{1 \leq i \leq m}$ and $(Y_i)_{1 \leq i \leq m}$ with the $X'_i$ $G$-valued, one has
  $$ k - D[(X'_i)_{1 \leq i \leq m} | (Y_i)_{1 \leq i \leq m}] \leq \eta \sum_{i=1}^m d[X_i; X'_i|Y_i].$$ -/
lemma sub_condMultiDistance_le {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀]
    {p : multiRefPackage G Ω₀} {Ω : Fin p.m → Type u} {hΩ : ∀ i, MeasureSpace (Ω i)}
    (hΩprob : ∀ i, IsProbabilityMeasure (hΩ i).volume) {X : ∀ i, Ω i → G}
    (hmeasX : ∀ i, Measurable (X i)) (h_min : multiTauMinimizes p Ω hΩ X)
    {Ω' : Fin p.m → Type u} {hΩ' : ∀ i, MeasureSpace (Ω' i)}
    (hΩ'prob: ∀ i, IsProbabilityMeasure (hΩ' i).volume)
    {X' : ∀ i, Ω' i → G} (hmeasX': ∀ i, Measurable (X' i))
    {S : Type u} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Y : ∀ i, Ω' i → S} (hY : ∀ i, Measurable (Y i) ):
    D[X; hΩ] - D[X'|Y; hΩ'] ≤ p.η * ∑ i, d[X i ; (hΩ i).volume # X' i | Y i; (hΩ' i).volume] := by
  set μ := fun ω : Fin p.m → S ↦ ∏ i : Fin p.m, Measure.real ℙ (Y i ⁻¹' {ω i})

  have probmes (i : Fin p.m) : ∑ ωi : S, (Measure.real ℙ (Y i ⁻¹' {ωi})) = 1 := by
    convert sum_measureReal_singleton (s := Finset.univ) (μ := .map (Y i) ℙ) with ω _ i _
    · exact (map_measureReal_apply (hY i) ( .singleton ω)).symm
    replace hΩ'prob := hΩ'prob i
    rw [map_measureReal_apply (hY i) (Finset.measurableSet _), Finset.coe_univ, Set.preimage_univ,
      measureReal_univ_eq_one]
-- μ has total mass one
  have total : ∑ (ω : Fin p.m → S), μ ω = 1 := calc
    _ = ∏ i, ∑ ωi, Measure.real ℙ (Y i ⁻¹' {ωi}) := by
      convert Finset.sum_prod_piFinset Finset.univ _ with ω _ i _
      rfl
    _ = ∏ i, 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact probmes i
    _ = 1 := by
      simp only [Finset.prod_const_one]

  calc
    _ = ∑ (ω : Fin p.m → S), μ ω * D[X; hΩ] -
        ∑ (ω : Fin p.m → S), μ ω * D[X' ; fun i ↦ MeasureSpace.mk ℙ[|Y i ⁻¹' {ω i}]] := by
      congr
      rw [← Finset.sum_mul, total, one_mul]
    _ = ∑ (ω : Fin p.m → S), μ ω * (D[X; hΩ] - D[X' ; fun i ↦ MeasureSpace.mk ℙ[|Y i ⁻¹' {ω i}]]) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro _ _
      exact (mul_sub_left_distrib _ _ _).symm
    _ ≤ ∑ (ω : Fin p.m → S), μ ω * (p.η * ∑ i, d[X i ; (hΩ i).volume # X' i; ℙ[|Y i ⁻¹' {ω i}] ]) := by
      apply Finset.sum_le_sum
      intro ω _
      rcases eq_or_ne (μ ω) 0 with hω | hω
      · simp [hω]
      gcongr
      let hΩ'_cond i := MeasureSpace.mk ℙ[|Y i ⁻¹' {ω i}]
      have hΩ'prob_cond i : IsProbabilityMeasure (hΩ'_cond i).volume := by
        refine cond_isProbabilityMeasure ?_
        contrapose! hω
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [measureReal_def, hω, ENNReal.toReal_zero]
      exact sub_multiDistance_le hΩprob hmeasX h_min hΩ'prob_cond hmeasX'
    _ = p.η * ∑ i, ∑ (ω : Fin p.m → S), μ ω * d[X i ; (hΩ i).volume # X' i; ℙ[|Y i ⁻¹' {ω i}] ] := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      congr with i
      let f := fun j ↦ (fun ωj ↦ (Measure.real ℙ (Y j ⁻¹' {ωj})) *
        (if i=j then d[X i ; ℙ # X' i ; ℙ[|Y i ⁻¹' {ωj}]] else 1))
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
            rw [condRuzsaDist'_eq_sum' (hmeasX' i) (hY i), ← hij]
          simp only [mul_ite, mul_one, hij, ↓reduceIte, f]
          exact probmes j
        _ = _ := by
          simp only [Finset.prod_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- With the notation of the previous lemma, we have
  \begin{equation}\label{5.3-conv}
    k - D[ X'_{[m]} | Y_{[m]} ] \leq \eta \sum_{i=1}^m d[X_{\sigma(i)};X'_i|Y_i]
  \end{equation}
for any permutation $\sigma : \{1,\dots,m\} \rightarrow \{1,\dots,m\}$. -/
lemma sub_condMultiDistance_le' {G Ω₀ : Type u} [MeasurableFinGroup G] [MeasureSpace Ω₀]
    {p : multiRefPackage G Ω₀} {Ω : Fin p.m → Type u} {hΩ : ∀ i, MeasureSpace (Ω i)}
    (hΩprob : ∀ i, IsProbabilityMeasure (hΩ i).volume)
    {X : ∀ i, Ω i → G} (hmeasX : ∀ i, Measurable (X i)) (h_min : multiTauMinimizes p Ω hΩ X)
    {Ω' : Fin p.m → Type u} {hΩ' : ∀ i, MeasureSpace (Ω' i)}
    (hΩ'prob: ∀ i, IsProbabilityMeasure (hΩ' i).volume) {X' : ∀ i, Ω' i → G}
    (hmeasX': ∀ i, Measurable (X' i))
    {S : Type u} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Y : ∀ i, Ω' i → S} (hY : ∀ i, Measurable (Y i)) (φ : Equiv.Perm (Fin p.m)) :
    D[X; hΩ] - D[X'|Y; hΩ'] ≤
      p.η * ∑ i, d[X (φ i) ; (hΩ (φ i)).volume # X' i | Y i; (hΩ' i).volume ] := by
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
      apply sub_condMultiDistance_le hΩφprob hmeasXφ _ hΩ'prob hmeasX' hY
      intro Ω'' hΩ'' hprob X'' hX''
      calc
      _ = multiTau p Ω hΩ X := by
        dsimp [multiTau]
        congr 1
        · exact multiDist_of_perm hΩ hΩprob X φ
        congr 1
        exact Fintype.sum_equiv φ _ _ fun _ ↦ rfl
      _ ≤ multiTau p Ω'' hΩ'' X'' := h_min Ω'' hΩ'' hprob X'' hX''
