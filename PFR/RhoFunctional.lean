module

public import PFR.ForMathlib.ThreeVariables
public import PFR.Kullback
public import PFR.Main

/-!
# The rho functional

Definition of the rho functional and basic facts
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Function Measure Filter
open scoped Pointwise ENNReal Topology
universe uG

section

variable {G : Type uG} [AddCommGroup G] [Finite G] [hGm : MeasurableSpace G]
  [DiscreteMeasurableSpace G] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X Y Z : Ω → G} {A : Finset G}


/-- The set of possible values of $D_{KL}(X \Vert U_A + T)$, where $U_A$ is uniform on $A$ and
$T$ ranges over $G$-valued random variables independent of $U_A$. We also require an absolute
continuity condition so that the KL divergence makes sense in `ℝ`.

To avoid universe issues, we express this using measures on `G`, but the equivalence with the
above point of view follows from `rhoMinus_le` below. -/
noncomputable def rhoMinusSet
    (X : Ω → G) (A : Finset G) (μ : Measure Ω) : Set ℝ :=
  {x : ℝ | ∃ (μ' : Measure G), IsProbabilityMeasure μ' ∧
    (∀ y, (μ'.prod (uniformOn A)).map (Prod.fst + Prod.snd) {y} = 0 → μ.map X {y} = 0) ∧
    x = KL[X ; μ # Prod.fst + Prod.snd ; μ'.prod (uniformOn A)]}

lemma map_prod_uniformOn_ne_zero {y : G} (hA : A.Nonempty)
    {μ : Measure G} [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) :
    (μ.prod (uniformOn A)).map (Prod.fst + Prod.snd) {y} ≠ 0 := by
  cases nonempty_fintype G
  intro h
  obtain ⟨a, ha⟩ : ∃ x, x ∈ A := by exact hA
  let ν := uniformOn (A : Set G)
  have : IsProbabilityMeasure ν :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  have h_indep : IndepFun Prod.fst Prod.snd (μ.prod ν) := ProbabilityTheory.indepFun_fst_snd
  rw [h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp)] at h
  specialize h a (Finset.mem_univ a)
  have : (Measure.map Prod.snd (μ.prod ν)) {a} ≠ 0 := by
    simp [Measure.map_snd_prod, ν, uniformOn_apply_singleton_of_mem (by exact ha) A.finite_toSet]
  simp only [mul_eq_zero, this, false_or, Measure.map_fst_prod] at h
  simp only [measure_univ, one_smul] at h
  exact hμ (y - a) h

lemma nonempty_rhoMinusSet [IsZeroOrProbabilityMeasure μ] (hA : A.Nonempty) :
    Set.Nonempty (rhoMinusSet X A μ) := by
  rcases eq_zero_or_isProbabilityMeasure μ with hμ | hμ
  · refine ⟨0, ⟨uniformOn (A : Set G), isProbabilityMeasure_uniformOn A.finite_toSet hA,
      by simp [hμ], by simp [hμ, KLDiv]⟩⟩
  set μ' := uniformOn (univ : Set G) with hμ'
  have : IsProbabilityMeasure μ' := isProbabilityMeasure_uniformOn finite_univ univ_nonempty
  refine ⟨_, ⟨μ', this, fun y hy ↦ (map_prod_uniformOn_ne_zero hA ?_ hy).elim, rfl⟩⟩
  intro x
  simp [hμ', uniformOn_apply_singleton_of_mem (mem_univ _) finite_univ]

lemma nonneg_of_mem_rhoMinusSet [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) {x : ℝ} (hx : x ∈ rhoMinusSet X A μ) : 0 ≤ x := by
  rcases hx with ⟨μ, hμ, habs, rfl⟩
  exact KLDiv_nonneg hX (by fun_prop) habs

lemma bddBelow_rhoMinusSet [IsZeroOrProbabilityMeasure μ] (hX : Measurable X) :
    BddBelow (rhoMinusSet X A μ) :=
  ⟨0, fun _ hx ↦ nonneg_of_mem_rhoMinusSet hX hx⟩

lemma rhoMinusSet_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → G}
    (h : IdentDistrib X X' μ μ') : rhoMinusSet X A μ = rhoMinusSet X' A μ' := by
  have I (μ'' : Measure G) : KL[X ; μ # Prod.fst + Prod.snd ; μ''.prod (uniformOn (A : Set G))] =
      KL[X' ; μ' # Prod.fst + Prod.snd ; μ''.prod (uniformOn (A : Set G))] := by
    apply ProbabilityTheory.IdentDistrib.KLDiv_eq _ _ h
    exact .refl (by fun_prop)
  simp only [rhoMinusSet, h.map_eq, I]

/-- For any $G$-valued random variable $X$, we define $\rho^-(X)$ to be the infimum of
$D_{KL}(X \Vert U_A + T)$, where $U_A$ is uniform on $A$ and $T$ ranges over $G$-valued random
variables independent of $U_A$. -/
noncomputable def rhoMinus (X : Ω → G) (A : Finset G) (μ : Measure Ω) : ℝ :=
  sInf (rhoMinusSet X A μ)

@[inherit_doc rhoMinus] notation3:max "ρ⁻[" X " ; " μ " # " A "]" => rhoMinus X A μ

@[inherit_doc rhoMinus] notation3:max "ρ⁻[" X " # " A "]" => rhoMinus X A volume

lemma rhoMinus_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {X' : Ω' → G} {μ' : Measure Ω'}
    (h : IdentDistrib X X' μ μ') : ρ⁻[X ; μ # A] = ρ⁻[X' ; μ' # A] := by
  simp [rhoMinus, rhoMinusSet_eq_of_identDistrib h]

lemma rhoMinus_le_def [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) {μ' : Measure G} [IsProbabilityMeasure μ']
    (habs : ∀ y, (μ'.prod (uniformOn A)).map (Prod.fst + Prod.snd) {y} = 0 → μ.map X {y} = 0) :
    ρ⁻[X ; μ # A] ≤ KL[X ; μ # Prod.fst + Prod.snd ; μ'.prod (uniformOn A)] := by
  apply csInf_le (bddBelow_rhoMinusSet hX)
  exact ⟨μ', by infer_instance, habs, rfl⟩

lemma rhoMinus_le [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hA : A.Nonempty)
    {Ω' : Type*} [MeasurableSpace Ω'] {T : Ω' → G} {U : Ω' → G} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] (hunif : IsUniform A U μ') (hT : Measurable T)
    (hU : Measurable U) (h_indep : IndepFun T U μ')
    (habs : ∀ y, (μ'.map (T + U)) {y} = 0 → μ.map X {y} = 0) :
    ρ⁻[X ; μ # A] ≤ KL[X ; μ # T + U ; μ'] := by
  cases nonempty_fintype G
  have : IsProbabilityMeasure (μ'.map T) := isProbabilityMeasure_map hT.aemeasurable
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  have E : μ'.map U = uniformOn (A : Set G) := hunif.map_eq_uniformOn hU A.finite_toSet hA
  have M : (Measure.map (Prod.fst + Prod.snd) ((μ'.map T).prod (uniformOn ↑A))) =
      (Measure.map (T + U) μ') := by
    ext s _
    rw [h_indep.map_add_eq_sum hT hU]
    have : IndepFun Prod.fst Prod.snd ((μ'.map T).prod (uniformOn (A : Set G))) :=
      ProbabilityTheory.indepFun_fst_snd
    rw [this.map_add_eq_sum measurable_fst measurable_snd,
      Measure.map_fst_prod, Measure.map_snd_prod]
    simp [E]
  apply csInf_le (bddBelow_rhoMinusSet hX)
  simp only [rhoMinusSet, Set.mem_setOf_eq]
  exact ⟨μ'.map T, isProbabilityMeasure_map hT.aemeasurable, by rwa [M], by simp [KLDiv, M]⟩

/-- We have $\rho^-(X) \geq 0$. -/
lemma rhoMinus_nonneg [IsZeroOrProbabilityMeasure μ]
    {X : Ω → G} {A : Finset G} (hX : Measurable X) : 0 ≤ ρ⁻[X ; μ # A] :=
  Real.sInf_nonneg (fun _ hx ↦ nonneg_of_mem_rhoMinusSet hX hx)

lemma rhoMinus_zero_measure (hP : μ = 0)
    {X : Ω → G} {A : Finset G} : ρ⁻[X ; μ # A] = 0 := by
  have : ∃ (μ' : Measure G), IsProbabilityMeasure μ' :=
    ⟨uniformOn Set.univ, isProbabilityMeasure_uniformOn finite_univ univ_nonempty⟩
  simp [rhoMinus, rhoMinusSet, hP, this, KLDiv]

private lemma rhoMinus_continuous_aux1 (hX : Measurable X) (hA : A.Nonempty)
    {r : ℝ} (hr : ρ⁻[X ; μ # A] < r)
    [IsProbabilityMeasure μ] [TopologicalSpace G] [DiscreteTopology G] :
    ∃ (μ' : Measure G), IsProbabilityMeasure μ' ∧ (∀ y, 0 < μ' {y}) ∧
    KL[X ; μ # Prod.fst + Prod.snd ; μ'.prod (uniformOn A)] < r := by
  rcases (csInf_lt_iff (bddBelow_rhoMinusSet hX) (nonempty_rhoMinusSet hA)).1 hr
    with ⟨-, ⟨μ₀, hPμ₀, habs, rfl⟩, h₀⟩
  let μ₀P : ProbabilityMeasure G := ⟨μ₀, hPμ₀⟩
  obtain ⟨u, -, u_mem, hu⟩ := exists_seq_strictAnti_tendsto' (x := (0 : ℝ≥0∞)) zero_lt_one
  let ν : ℕ → Measure G := fun n ↦ (1 - u n) • μ₀ + u n • uniformOn univ
  have : IsProbabilityMeasure (uniformOn (univ : Set G)) :=
    isProbabilityMeasure_uniformOn finite_univ univ_nonempty
  have P n : IsProbabilityMeasure (ν n) := by
    simp only [isProbabilityMeasure_iff, coe_add, coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one, ν]
    rw [ENNReal.sub_add_eq_add_sub, ENNReal.add_sub_cancel_right]
    · exact ne_of_lt ((u_mem n).2.trans ENNReal.one_lt_top)
    · exact (u_mem n).2.le
    · exact ne_of_lt ((u_mem n).2.trans ENNReal.one_lt_top)
  let νP n : ProbabilityMeasure G := ⟨ν n, P n⟩
  have L : Tendsto νP atTop (𝓝 μ₀P) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_apply_tendsto_ennreal]
    intro g
    simp only [ProbabilityMeasure.coe_mk, coe_add, coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, νP, ν, μ₀P]
    have : 𝓝 (μ₀ {g}) = 𝓝 ((1 - 0) * μ₀ {g} + 0 * (uniformOn univ {g})) := by simp
    rw [this]
    apply Tendsto.add
    · apply ENNReal.Tendsto.mul_const _ (by simp)
      exact ENNReal.Tendsto.sub tendsto_const_nhds hu (by simp)
    · exact ENNReal.Tendsto.mul_const hu (by simp)
  let PA : ProbabilityMeasure G := ⟨uniformOn A, isProbabilityMeasure_uniformOn (A.finite_toSet) hA⟩
  have : Tendsto (fun n ↦ (νP n).prod PA) atTop (𝓝 (μ₀P.prod PA)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (μ₀P, PA)).comp (f := fun n ↦ (νP n, PA)) <|
      L.prodMk_nhds tendsto_const_nhds
  have C : Continuous (Prod.fst + Prod.snd : G × G → G) := by fun_prop
  have Z := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ this
    (f := Prod.fst + Prod.snd) C
  have M : ∀ (x : G), ((μ₀P.prod PA).map C.aemeasurable) {x} = 0 → (Measure.map X μ) {x} = 0 := by
    intro x hx
    apply habs
    simpa [μ₀P, PA] using hx
  have T := tendsto_KLDiv_id_right (X := X) (μ := μ) (G := G) Z M
  have : KL[X ; μ # id ; Measure.map (Prod.fst + Prod.snd) (μ₀.prod (uniformOn ↑A))]
      = KL[X ; μ # Prod.fst + Prod.snd ; (μ₀.prod (uniformOn ↑A))] := by
    simp [KLDiv]
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod,
    ProbabilityMeasure.coe_mk, this, PA, μ₀P] at T
  rcases ((tendsto_order.1 T).2 _ h₀).exists with ⟨n, hn⟩
  refine ⟨ν n, P n, fun y ↦ ?_, ?_⟩
  · simp [(u_mem n).1, ν, uniformOn_apply_singleton_of_mem (mem_univ _) finite_univ]
  · have : KL[X ; μ # id ; Measure.map (Prod.fst + Prod.snd) ((ν n).prod (uniformOn ↑A))]
      =  KL[X ; μ # Prod.fst + Prod.snd ; ((ν n).prod (uniformOn ↑A))] := by simp [KLDiv]
    simpa [νP, this] using hn

private lemma rhoMinus_continuous_aux2 (hA : A.Nonempty) {μ : ProbabilityMeasure G}
    {r : ℝ} (hr : ρ⁻[id ; μ # A] < r) [TopologicalSpace G] [DiscreteTopology G] :
    ∀ᶠ (μ' : ProbabilityMeasure G) in 𝓝 μ, ρ⁻[id ; μ' # A] < r := by
  obtain ⟨ν, νP, ν_pos, hν⟩ : ∃ (ν : Measure G), IsProbabilityMeasure ν ∧ (∀ y, 0 < ν {y}) ∧
      KL[id ; μ # Prod.fst + Prod.snd ; ν.prod (uniformOn A)] < r := by
    apply rhoMinus_continuous_aux1 measurable_id hA hr
  have : Tendsto (fun (μ' : ProbabilityMeasure G) ↦
        KL[id ; μ' # Prod.fst + Prod.snd ; ν.prod (uniformOn A)])
      (𝓝 μ) (𝓝 (KL[id ; μ # Prod.fst + Prod.snd ; ν.prod (uniformOn A)])) :=
    tendsto_KLDiv_id_left tendsto_id
  filter_upwards [(tendsto_order.1 this).2 _ hν] with μ' hμ'
  apply lt_of_le_of_lt _ hμ'
  apply rhoMinus_le_def measurable_id
  intro y hy
  contrapose hy
  exact map_prod_uniformOn_ne_zero hA (fun x ↦ (ν_pos x).ne')

private lemma rhoMinus_continuous_aux3 (hA : A.Nonempty) {μ : ProbabilityMeasure G}
    {ε : ℝ} (hε : 0 < ε) [TopologicalSpace G] [DiscreteTopology G] :
    ∀ᶠ (μ' : ProbabilityMeasure G) in 𝓝 μ, ρ⁻[id ; μ # A] < ρ⁻[id ; μ' # A] + ε := by
  cases nonempty_fintype G
  obtain ⟨c, c_pos, hc⟩ : ∃ c > 0, ∀ g,
      μ.toMeasure.real {g} ≠ 0 → c ≤ μ.toMeasure.real {g} := by
    let B := {g | μ.toMeasure.real {g} ≠ 0}
    have : B.Finite := toFinite B
    have : B.Nonempty := by
      by_contra! H
      simp [-ProbabilityMeasure.measureReal_eq_coe_coeFn, ne_eq, -NNReal.coe_eq_zero,
        eq_empty_iff_forall_notMem, mem_setOf_eq,
        Decidable.not_not, B] at H
      have : ∑ g, μ.toMeasure.real {g} = 1 := by
        simp [-ProbabilityMeasure.measureReal_eq_coe_coeFn]
      simp [H] at this
    have Bn : (B.toFinset.image (fun g ↦ μ.toMeasure.real {g})).Nonempty := by
      simpa using this
    let c := (B.toFinset.image (fun g ↦ μ.toMeasure.real {g})).min' Bn
    refine ⟨c, ?_, fun g hg ↦ ?_⟩
    · have : c ∈ B.toFinset.image (fun g ↦ ((μ : Measure G) {g}).toReal) := Finset.min'_mem _ _
      simp only [ne_eq, toFinset_setOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, B] at this
      rcases this with ⟨g, hg, cg⟩
      rw [← cg]
      exact lt_of_le_of_ne (by simp) (Ne.symm hg)
    · apply Finset.min'_le
      simp only [ne_eq, Finset.mem_image, mem_toFinset]
      exact ⟨g, hg, rfl⟩
  let C := (ρ⁻[id ; μ # A] + H[id ; (μ : Measure G)] + 3 * c / 2) / (c / 2)
  have C_nonneg : 0 ≤ C := by
    have : 0 ≤ ρ⁻[id ; μ # A] := by
      apply rhoMinus_nonneg measurable_id
    have : 0 ≤ H[id ; (μ : Measure G)] := entropy_nonneg _ _
    positivity
  obtain ⟨δ, δpos, hδc, hδ⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < c / 2 ∧ δ * (2 + C * Fintype.card G) < ε := by
    refine ⟨(min (c / 2) (ε / (2 + C * Fintype.card G))) / 2, ?_, ?_, ?_⟩
    · positivity
    · exact (half_lt_self (by positivity)).trans_le (min_le_left _ _)
    · rw [← lt_div_iff₀ (by positivity)]
      exact (half_lt_self (by positivity)).trans_le (min_le_right _ _)
  have E₁ : ∀ᶠ (μ' : ProbabilityMeasure G) in 𝓝 μ,
      |H[id ; (μ' : Measure G)] - H[id ; (μ : Measure G)]| < δ := by
    have : Tendsto (fun (μ' : ProbabilityMeasure G) ↦ H[id ; (μ' : Measure G)])
        (𝓝 μ) (𝓝 (H[id ; (μ : Measure G)])) :=
      continuous_entropy_restrict_probabilityMeasure.continuousAt
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 this)).2 _ δpos
  have E₂ : ∀ᶠ (μ' : ProbabilityMeasure G) in 𝓝 μ, ∀ g,
      |μ'.toMeasure.real {g} - μ.toMeasure.real {g}| < δ := by
    rw [eventually_all]
    intro g
    have : Tendsto (fun (μ' : ProbabilityMeasure G) ↦ ((μ' : Measure G) {g}).toReal)
          (𝓝 μ) (𝓝 (((μ : Measure G) {g}).toReal)) := by
      rw [ENNReal.tendsto_toReal_iff (by simp) (by simp)]
      exact (ProbabilityMeasure.tendsto_iff_forall_apply_tendsto_ennreal _ _).1 tendsto_id _
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 this)).2 _ δpos
  have M : ρ⁻[id ; μ # A] < ρ⁻[id ; μ # A] + δ := by linarith
  filter_upwards [rhoMinus_continuous_aux2 hA M, E₁, E₂] with μ' h' h₁ h₂
  have h₃ g (hg : μ.toMeasure.real {g} ≠ 0) : c/2 ≤ μ'.toMeasure.real {g} := by
    have : c ≤ μ.toMeasure.real {g} := hc _ hg
    linarith [neg_le_of_abs_le (h₂ g).le]
  have : ρ⁻[id ; μ' # A] < ρ⁻[id ; μ' # A] + δ := by linarith
  have : ∃ b ∈ rhoMinusSet id A μ', b < ρ⁻[id ; μ' # A] + δ :=
    (csInf_lt_iff (bddBelow_rhoMinusSet (μ := μ') measurable_id (A := A))
    (nonempty_rhoMinusSet hA (X := id) (μ := μ'))).1 this
  rcases this with ⟨-, ⟨ν, νP, h'_abs, rfl⟩, h⟩
  simp only [Measure.map_id] at h'_abs
  set m := Measure.map (Prod.fst + Prod.snd) (ν.prod (uniformOn A)) with hm
  have m_nonpos g : log (m {g}).toReal ≤ 0 := by
    apply log_nonpos (by simp)
    have : m {g} ≤ 1 := prob_le_one
    simpa using ENNReal.toReal_mono (by simp) this
  have h_abs : ∀ g, m {g} = 0 → (μ : Measure G) {g} = 0 := by
    intro y hy
    have Z := h'_abs y hy
    contrapose! Z
    intro hy
    have : μ.toMeasure.real {y} ≠ 0 := by simpa [measureReal_eq_zero_iff] using Z
    have T := h₃ _ this
    simp [hy, measureReal_def] at T
    linarith
  have I₀ : KL[id ; μ' # Prod.fst + Prod.snd ; ν.prod (uniformOn A)]
      = - H[id ; (μ' : Measure G)] - ∑ g, μ'.toMeasure.real {g} * log (m.real {g}) := by
    rw [KLDiv_eq_sum, entropy_eq_sum, tsum_fintype, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
    congr with g
    simp only [Measure.map_id, negMulLog, neg_mul]
    rcases eq_or_ne (μ'.toMeasure.real {g}) 0 with h | h
    · simp [h]
    rw [log_div, hm]
    · ring
    · exact h
    · contrapose! h
      simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h ⊢
      apply h'_abs _ (by simpa [ENNReal.toReal_eq_zero_iff] using h)
  have M g (hg : μ.toMeasure.real {g} ≠ 0) : |log (m.real {g})| ≤ C := by
    rw [le_div_iff₀' (by positivity)]
    calc
    (c / 2) * |log (m.real {g})|
    _ ≤ μ'.toMeasure.real {g} * |log (m.real {g})| := by
      gcongr
      apply h₃ _ (by simpa [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] using hg)
    _ ≤ ∑ g, ((μ' : Measure G) {g}).toReal * |log ((m {g}).toReal)| := by
      apply Finset.single_le_sum (a := g) (fun i hi ↦ by positivity) (Finset.mem_univ g)
    _ = ∑ g, ((μ' : Measure G) {g}).toReal * (-log ((m {g}).toReal)) := by
      congr with g
      rw [abs_of_nonpos (m_nonpos g)]
    _ = KL[id ; μ' # Prod.fst + Prod.snd ; ν.prod (uniformOn A)] + H[id ; (μ' : Measure G)] := by
      simp_rw [I₀, mul_neg, Finset.sum_neg_distrib]
      abel
    _ ≤ (ρ⁻[id ; μ' # A] + δ) + H[id ; (μ' : Measure G)] := by linarith
    _ ≤ ((ρ⁻[id ; μ # A] + δ) + δ) + (H[id ; (μ : Measure G)] + δ) := by
      gcongr
      linarith [le_of_abs_le h₁.le]
    _ ≤ ρ⁻[id ; μ # A] + H[id ; (μ : Measure G)] + 3 * c / 2 := by linarith
  calc
  ρ⁻[id ; μ # A]
  _ ≤ KL[id ; μ # Prod.fst + Prod.snd ; ν.prod (uniformOn A)] :=
    rhoMinus_le_def measurable_id (by simpa using h_abs)
  _ = - H[id ; (μ : Measure G)] - ∑ g, μ.toMeasure.real {g} * log (m.real {g}) := by
    rw [KLDiv_eq_sum, entropy_eq_sum, tsum_fintype, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
    congr with g
    simp only [Measure.map_id, negMulLog, neg_mul]
    rcases eq_or_ne (μ.toMeasure.real {g}) 0 with h | h
    · simp [h]
    rw [log_div, hm]
    · ring
    · exact h
    · contrapose! h
      simp only [measureReal_def, ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] at h ⊢
      exact h_abs _ h
  _ ≤ - H[id ; (μ : Measure G)] - ∑ g ∈ {g | μ.toMeasure.real {g} ≠ 0},
        μ.toMeasure.real {g} * log (m.real {g}) := by
    gcongr
    · intro g hg h'g
      simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
        Decidable.not_not] at h'g
      simp [h'g]
    · exact Finset.filter_subset _ _
   _ ≤ - H[id ; (μ : Measure G)] - ∑ g ∈ {g | μ.toMeasure.real {g} ≠ 0},
        (μ'.toMeasure.real {g} + δ) * log (m.real {g}) := by
    apply sub_le_sub le_rfl
    apply Finset.sum_le_sum (fun g hg ↦ ?_)
    apply mul_le_mul_of_nonpos_right _ (m_nonpos g)
    linarith [neg_le_of_abs_le (h₂ g).le]
  _  ≤ - H[id ; (μ : Measure G)] - (∑ g ∈ {g | μ.toMeasure.real {g} ≠ 0},
          μ'.toMeasure.real {g} * log (m.real {g})
        + ∑ g ∈ {g | μ.toMeasure.real {g} ≠ 0}, δ * (-C)) := by
    rw [← Finset.sum_add_distrib]
    gcongr with g hg
    rw [add_mul]
    gcongr
    rw [neg_le]
    exact (neg_le_abs _).trans (M g (by simpa using hg))
  _ ≤ (-H[id ; (μ' : Measure G)] + δ) + (- ∑ g, μ'.toMeasure.real {g} * log (m.real {g})
        + Fintype.card G * (δ * C)) := by
    simp only [mul_neg, Finset.sum_const, nsmul_eq_mul, sub_eq_add_neg, neg_add, ←
      Finset.sum_neg_distrib, neg_neg]
    gcongr
    · linarith [le_of_abs_le h₁.le]
    · intro g hg h'g
      rw [← neg_mul, neg_mul_comm]
      have T := neg_nonneg.2 (m_nonpos g)
      positivity
    · exact Finset.filter_subset _ _
    · exact Finset.card_le_univ _
  _ = KL[id ; μ' # Prod.fst + Prod.snd ; ν.prod (uniformOn A)] + δ * (1 + C * Fintype.card G) := by
    rw [I₀]
    ring
  _ ≤ (ρ⁻[id ; μ' # A] + δ) + δ * (1 + C * Fintype.card G) := by linarith
  _ = ρ⁻[id ; μ' # A] + δ * (2 + C * Fintype.card G) := by ring
  _ < ρ⁻[id ; μ' # A] + ε := by linarith

lemma rhoMinus_continuous [TopologicalSpace G] [DiscreteTopology G] (hA : A.Nonempty) :
    Continuous (fun (μ : ProbabilityMeasure G) ↦ ρ⁻[id ; μ # A]) := by
  apply continuous_iff_continuousAt.2 (fun μ ↦ ?_)
  refine tendsto_order.2 ⟨fun r hr ↦ ?_, fun r hr ↦ rhoMinus_continuous_aux2 hA hr⟩
  dsimp at hr
  have : 0 < ρ⁻[id ; μ # A] - r := by linarith
  filter_upwards [rhoMinus_continuous_aux3 hA this (μ := μ)] with μ' hμ'
  linarith

/-- For any $G$-valued random variable $X$, we define
$\rho^+(X) := \rho^-(X) + \bbH(X) - \bbH(U_A)$. -/
noncomputable def rhoPlus (X : Ω → G) (A : Finset G) (μ : Measure Ω) : ℝ :=
  ρ⁻[X ; μ # A] + H[ X ; μ ] - log (Nat.card A)

@[inherit_doc rhoPlus] notation3:max "ρ⁺[" X " ; " μ " # " A "]" => rhoPlus X A μ

@[inherit_doc rhoPlus] notation3:max "ρ⁺[" X " # " A "]" => rhoPlus X A volume

lemma rhoPlus_continuous [TopologicalSpace G] [DiscreteTopology G] (hA : A.Nonempty) :
    Continuous (fun (μ : ProbabilityMeasure G) ↦ ρ⁺[id ; μ # A]) := by
  apply Continuous.add
  · apply Continuous.add
    · apply rhoMinus_continuous hA
    · apply continuous_entropy_restrict_probabilityMeasure
  · exact continuous_const

lemma rhoPlus_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {X' : Ω' → G} {μ' : Measure Ω'}
    (h : IdentDistrib X X' μ μ') : ρ⁺[X ; μ # A] = ρ⁺[X' ; μ' # A] := by
  simp [rhoPlus, rhoMinus_eq_of_identDistrib h, h.entropy_congr]

omit [MeasurableSpace G] [DiscreteMeasurableSpace G] in
lemma bddAbove_card_inter_add {A H : Set G} :
    BddAbove {Nat.card (A ∩ (t +ᵥ H) : Set G) | t : G} := by
  refine ⟨Nat.card A, fun k hk ↦ ?_⟩
  simp only [mem_setOf_eq] at hk
  rcases hk with ⟨t, rfl⟩
  exact Nat.card_mono (toFinite _) inter_subset_left

omit [MeasurableSpace G] [DiscreteMeasurableSpace G] in
lemma exists_mem_card_inter_add (H : AddSubgroup G) {A : Set G} (hA : A.Nonempty) :
    ∃ k > 0, k ∈ {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} := by
  rcases hA with ⟨t, ht⟩
  have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) := by
    apply Nonempty.to_subtype
    refine ⟨t, ht, ?_⟩
    exact mem_vadd_set.2 ⟨0, zero_mem H, by simp⟩
  refine ⟨Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G), Nat.card_pos, ?_⟩
  simp only [mem_setOf_eq, exists_apply_eq_apply]

omit [MeasurableSpace G] [DiscreteMeasurableSpace G] in
lemma exists_card_inter_add_eq_sSup (H : AddSubgroup G) {A : Set G} (hA : A.Nonempty) :
    ∃ t : G, (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)
        = sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G})
      ∧ 0 < Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) := by
  set k := sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G}
  rcases exists_mem_card_inter_add H hA with ⟨n, n_pos, hn⟩
  have : k ∈ {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} :=
    Nat.sSup_mem ⟨n, hn⟩ bddAbove_card_inter_add
  rcases this with ⟨t, ht⟩
  have : 0 < Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) := by
    apply lt_of_lt_of_le n_pos
    rw [ht]
    exact le_csSup bddAbove_card_inter_add hn
  exact ⟨t, ht, this⟩

private lemma le_rhoMinus_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G}
    {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    log (Nat.card A) -
      log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) ≤ ρ⁻[U ; μ # A] := by
  cases nonempty_fintype G
  apply le_csInf (nonempty_rhoMinusSet hA)
  rintro - ⟨μ', hμ', habs, rfl⟩
  let T : G × G → G := Prod.fst
  have hT : Measurable T := measurable_fst
  let UA : G × G → G := Prod.snd
  have hUA : Measurable UA := measurable_snd
  let _ : MeasureSpace (G × G) := ⟨μ'.prod (uniformOn (A : Set G))⟩
  have hprod : (ℙ : Measure (G × G)) = μ'.prod (uniformOn (A : Set G)) := rfl
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  have : IsProbabilityMeasure (Measure.map T ℙ) := by rw [hprod, Measure.map_fst_prod]; simp [hμ']
  have h_indep : IndepFun T UA := ProbabilityTheory.indepFun_fst_snd
  have hUA_unif : IsUniform A UA := by
    have : IsUniform A id (uniformOn (A : Set G)) := isUniform_uniformOn
    apply IsUniform.of_identDistrib this ?_ A.measurableSet
    exact measurePreserving_snd.identDistrib aemeasurable_id
  have : IsProbabilityMeasure (ℙ : Measure (G × G)) := by rw [hprod]; infer_instance
  let H' : Finset G := Set.Finite.toFinset (toFinite H)
  have hunif' : IsUniform H' U μ := by convert hunif; simp [H']
  have I₁ : KL[U ; μ # T + UA ; ℙ] =
      ∑ h ∈ H',
        1/(H : Set G).ncard * log ((1/(H : Set G).ncard) / (volume.map (T + UA)).real {h}) := by
    rw [KLDiv_eq_sum, ← Finset.sum_subset (Finset.subset_univ H')]; swap
    · intro x _ hH
      rw [map_measureReal_apply hU (measurableSet_singleton x), hunif.measureReal_preimage_of_nmem]
      · simp
      · simpa [H'] using hH
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    rw [hunif'.measureReal_preimage_of_mem' hU hi]
    congr <;> simp [H', ← Set.ncard_eq_toFinset_card]
  have I₂ : (∑ h ∈ H', 1/(H : Set G).ncard : ℝ) * log ((∑ h ∈ H', 1/(H : Set G).ncard : ℝ)
      / (∑ h ∈ H', (volume.map (T + UA)).real {h})) ≤ KL[U ; μ # T + UA ; ℙ] := by
    rw [I₁]
    apply Real.sum_mul_log_div_leq (by simp) (by simp) (fun i hi h'i ↦ ?_)
    have : (μ.map U).real {i} = 0 := by
      simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h'i ⊢
      simp [habs i h'i]
    simp [hunif'.measureReal_preimage_of_mem' hU hi, H.coe_nonempty.ne_empty, H'] at this
  have : (∑ h ∈ H', 1/(H : Set G).ncard : ℝ) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_one]
    rw [div_eq_one_iff_eq]
    · simp [H', ← Set.ncard_eq_toFinset_card]
    · simp [ne_of_gt, Set.ncard_eq_zero (Set.toFinite _)]
  simp only [this, one_mul] at I₂
  simp only [sum_measureReal_singleton, one_div, log_inv] at I₂
  apply le_trans _ I₂
  have I₃ : ((Measure.map (T + UA) ℙ).real ↑H')
      ≤ 1 * ((sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G}) / Nat.card A) := by
    have : ∑ x : G, ((Measure.map T ℙ).real {x}) = 1 := by simp
    rw [← this, add_comm, h_indep.symm.real_map_add_eq_sum hUA hT, Finset.sum_mul]
    simp_rw [
     map_measureReal_apply hUA (DiscreteMeasurableSpace.forall_measurableSet _),
      hUA_unif.measureReal_preimage hUA]
    simp only [probReal_univ, singleton_add, image_add_left, neg_neg, one_mul,
      Nat.card_eq_fintype_card, Fintype.card_coe, ge_iff_le, H']
    apply Finset.sum_le_sum (fun i _ ↦ ?_)
    gcongr
    apply le_csSup bddAbove_card_inter_add
    rw [inter_comm]
    refine ⟨-i, ?_⟩
    congr
    ext j
    simp [mem_vadd_set_iff_neg_vadd_mem]
  rw [one_mul] at I₃
  have : - log ((sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G}) / Nat.card A) ≤
      - log ((Measure.map (T + UA) ℙ).real ↑H') := by
    apply neg_le_neg
    apply log_le_log _ I₃
    apply lt_of_le_of_ne (by simp) (fun h ↦ ?_)
    rw [Eq.comm] at h
    simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h
    have : Measure.map (T + UA) ℙ ({(0 : G)} : Set G) = 0 := measure_mono_null (by simp [H']) h
    have Z := habs _ this
    rw [Measure.map_apply hU (measurableSet_singleton 0),
      hunif'.measure_preimage_of_mem hU (by simp [H'])] at Z
    simp at Z
  convert this using 1
  rw [log_div]
  · abel
  · norm_cast
    rcases exists_mem_card_inter_add H hA with ⟨k, k_pos, hk⟩
    exact (lt_of_lt_of_le k_pos (le_csSup bddAbove_card_inter_add hk)).ne'
  · norm_cast
    apply ne_of_gt
    have : Nonempty { x // x ∈ A } := hA.to_subtype
    exact Nat.card_pos

private lemma rhoMinus_le_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G}
    (t : G) {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty)
    (h'A : (A ∩ (t +ᵥ (H : Set G)) : Set G).Nonempty) (hU : Measurable U) :
    ρ⁻[U ; μ # A] ≤
      log (Nat.card A) - log (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)) := by
  cases nonempty_fintype G
  classical
  have mapU : .map U μ = uniformOn (H : Set G) :=
    hunif.map_eq_uniformOn hU (H : Set G).toFinite H.coe_nonempty
  obtain ⟨a, ha, h'a⟩ := by exact h'A
  rcases mem_vadd_set.1 h'a with ⟨v, vH, rfl⟩
  simp only [vadd_eq_add, Finset.mem_coe] at ha
  have P z : (fun x ↦ x - t) ⁻¹' {z} = {z + t} := by ext w; simp [sub_eq_iff_eq_add]
  set μ' := μ.map ((· - t) ∘ U) with hμ'
  have μ'_sing z : μ' {z} = uniformOn (H : Set G) {z + t} := by
    rw [hμ', ← Measure.map_map (by fun_prop) hU,
      Measure.map_apply (by fun_prop) (measurableSet_singleton _), mapU, P]
  have μ'_sing_real z : μ'.real {z} = (uniformOn (H : Set G)).real {z + t} := by
    rw [measureReal_def, μ'_sing]
    rfl
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  have : IsProbabilityMeasure μ' :=
    isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have h_indep : IndepFun Prod.fst Prod.snd (μ'.prod (uniformOn (A : Set G))) := indepFun_fst_snd
  apply csInf_le (bddBelow_rhoMinusSet hU)
  simp only [rhoMinusSet, Nat.card_eq_fintype_card, Fintype.card_coe, mem_setOf_eq]
  refine ⟨μ', this, fun y h ↦ ?_, ?_⟩
  · rw [mapU]
    apply uniformOn_apply_singleton_of_not_mem (fun yH ↦ ?_)
    rw [h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd,
      Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp), Measure.map_snd_prod,
      Measure.map_fst_prod] at h
    specialize h (t + v)
    simp only [Finset.mem_univ, measure_univ, one_smul,
      uniformOn_apply_singleton_of_mem (by exact ha) A.finite_toSet, Finset.coe_sort_coe,
      Nat.card_eq_fintype_card, Fintype.card_coe, one_div, μ'_sing, mul_eq_zero,
      ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, false_or, true_implies] at h
    rw [uniformOn_apply_singleton_of_mem _ (toFinite (H : Set G))] at h
    · simp at h
    · convert (H.sub_mem yH vH) using 1
      abel
  let H' : Finset G := Set.toFinset H
  have hunif' : IsUniform H' U μ := by convert hunif; ext; simp [H']
  rw [KLDiv_eq_sum, ← Finset.sum_subset (Finset.subset_univ H')]; swap
  · intro x _ hH
    rw [map_measureReal_apply hU (measurableSet_singleton x), hunif.measureReal_preimage_of_nmem]
    · simp
    · simpa [H'] using hH
  have :
    ∑ x ∈ H', (μ.map U).real {x} *
      log ((μ.map U).real {x} / ((μ'.prod (uniformOn ↑A)).map (Prod.fst + Prod.snd)).real {x})
      = ∑ x ∈ H', (1/(H : Set G).ncard) * log ((1/(H : Set G).ncard)
        / (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) / (Nat.card A * (H : Set G).ncard))) := by
    have (x) (hx : x ∈ H') : (μ.map U).real {x} = 1/(H : Set G).ncard := by
      rw [map_measureReal_apply hU (measurableSet_singleton _),
        hunif'.measureReal_preimage_of_mem hU hx]
      simp [H', ← Nat.card_coe_set_eq]
    congr! with x hx
    · exact this _ hx
    · exact this _ hx
    replace hx : x ∈ H := by simpa [H'] using hx
    have (y : G) : x - y + t ∈ H ↔ y ∈ t +ᵥ (H : Set G).toFinset := by
      simpa [sub_eq_add_neg, add_assoc, H.add_mem_cancel_left hx, ← Finset.neg_vadd_mem_iff]
        using H.neg_mem_iff (x := -t + y)
    rw [h_indep.real_map_add_singleton_eq_sum measurable_fst measurable_snd]
    simp [μ'_sing_real, toFinite, uniformOn_real_singleton, ← ite_and, div_eq_mul_inv, -mul_inv_rev,
      mul_inv, this, ← Finset.mem_inter, Finset.filter_mem_eq_inter]
  have C : H'.card = (H : Set G).ncard := by simp [H', ← Nat.card_coe_set_eq]
  simp only [this, one_div, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.sum_const, C,
    nsmul_eq_mul, ← mul_assoc]
  rw [mul_inv_cancel₀, one_mul]; swap
  · norm_cast
    exact Nat.card_pos.ne'
  have C₁ : Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) ≠ 0 := by
    have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) := h'A.to_subtype
    exact Nat.card_pos.ne'
  have C₃ : (H : Set G).ncard ≠ 0 := Nat.card_pos.ne'
  rw [← log_div (by positivity) (by simpa using C₁)]
  congr 1
  field_simp

/-- If $H$ is a finite subgroup of $G$, then
$\rho^-(U_H) = \log |A| - \log \max_t |A \cap (H+t)|$. -/
lemma rhoMinus_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G}
    {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    ρ⁻[U ; μ # A] = log (Nat.card A) -
      log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) := by
  apply le_antisymm _ (le_rhoMinus_of_subgroup hunif hA hU)
  rcases exists_card_inter_add_eq_sSup (A := A) H hA with ⟨t, ht, hpos⟩
  rw [← ht]
  have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) :=  (Nat.card_pos_iff.1 hpos).1
  exact rhoMinus_le_of_subgroup t hunif hA .of_subtype hU

/-- If $H$ is a finite subgroup of $G$, then
$\rho^+(U_H) = \log |H| - \log \max_t |A \cap (H+t)|$. -/
lemma rhoPlus_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G}
    {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    ρ⁺[U ; μ # A] = log ((H : Set G).ncard) -
      log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) := by
  have : H[U ; μ] = log ((H : Set G).ncard) := hunif.entropy_eq' (toFinite _) hU
  rw [rhoPlus, rhoMinus_of_subgroup hunif hA hU, this]
  abel

/-- We define $\rho(X) := (\rho^+(X) + \rho^-(X))/2$. -/
noncomputable def rho (X : Ω → G) (A : Finset G) (μ : Measure Ω) : ℝ :=
  (ρ⁻[X ; μ # A] + ρ⁺[X ; μ # A]) / 2

@[inherit_doc rho] notation3:max "ρ[" X " ; " μ " # " A "]" => rho X A μ

@[inherit_doc rho] notation3:max "ρ[" X " # " A "]" => rho X A volume


lemma rho_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {X' : Ω' → G} {μ' : Measure Ω'}
    (h : IdentDistrib X X' μ μ') : ρ[X ; μ # A] = ρ[X' ; μ' # A] := by
  simp [rho, rhoMinus_eq_of_identDistrib h, rhoPlus_eq_of_identDistrib h]

/-- We have $\rho(U_A) = 0$. -/
lemma rho_of_uniform [IsProbabilityMeasure μ]
    {U : Ω → G} {A : Finset G} (hunif : IsUniform A U μ) (hU : Measurable U)
    (hA : A.Nonempty) : ρ[U ; μ # A] = 0 := by
  have : H[U ; μ] = log (Nat.card A) := hunif.entropy_eq' (toFinite _) hU
  simp only [rho, rhoPlus, this, Nat.card_eq_fintype_card, Fintype.card_coe, add_sub_cancel_right,
    add_self_div_two]
  apply le_antisymm _ (rhoMinus_nonneg hU)
  have Z := rhoMinus_le hU hA (T := fun _ ↦ 0) hunif measurable_const hU
    (indepFun_const 0).symm (μ := μ)
  have : (fun x ↦ 0) + U = U := by ext y; simp
  simpa [this] using Z

/-- If $H$ is a finite subgroup of $G$, and $\rho(U_H) \leq r$, then there exists $t$ such
that $|A \cap (H+t)| \geq e^{-r} \sqrt{|A||H|}$, and $|H|/|A| \in [e^{-2r}, e^{2r}]$. -/
lemma rho_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G} {U : Ω → G}
    (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U)
    (r : ℝ) (hr : ρ[U ; μ # A] ≤ r) :
    ∃ t : G,
      exp (-r) * Nat.card A ^ (1/2 : ℝ) * (H : Set G).ncard ^ (1/2 : ℝ) ≤
        Nat.card ↑(↑A ∩ (t +ᵥ (H : Set G)))
      ∧ Nat.card A ≤ exp (2 * r) * (H : Set G).ncard
      ∧ (H : Set G).ncard ≤ exp (2 * r) * Nat.card A := by
  have hr' : ρ[U ; μ # A] ≤ r := hr
  have Hpos : 0 < ((H : Set G).ncard : ℝ) := by exact_mod_cast Nat.card_pos
  have : Nonempty A := hA.to_subtype
  have Apos : 0 < (Nat.card A : ℝ) := by exact_mod_cast Nat.card_pos
  simp only [rho] at hr
  rw [rhoMinus_of_subgroup hunif hA hU, rhoPlus_of_subgroup hunif hA hU] at hr
  rcases exists_card_inter_add_eq_sSup (A := A) H hA with ⟨t, ht, hpos⟩
  rw [← ht] at hr
  have Rm : 0 ≤ ρ⁻[U ; μ # A] := rhoMinus_nonneg hU
  have RM : 0 ≤ ρ⁺[U ; μ # A] := by
    rw [rhoPlus_of_subgroup hunif hA hU, ← ht, sub_nonneg]
    apply log_le_log (mod_cast hpos)
    norm_cast
    have : Nat.card (t +ᵥ (H : Set G) : Set G) = (H : Set G).ncard := by
      apply Nat.card_image_of_injective (add_right_injective t)
    rw [← this]
    exact Nat.card_mono (toFinite _) inter_subset_right
  have I : |log ((H : Set G).ncard) - log (Nat.card A)| ≤ 2 * r := calc
    |log ((H : Set G).ncard) - log (Nat.card A)|
    _ = |H[U ; μ] - log (Nat.card A)| := by rw [hunif.entropy_eq' (toFinite _) hU]
    _ = |ρ⁺[U ; μ # A] - ρ⁻[U ; μ # A]| := by congr 1; simp [rhoPlus]; abel
    _ ≤ ρ⁺[U ; μ # A] + ρ⁻[U ; μ # A] :=
      (abs_sub _ _).trans_eq (by simp [abs_of_nonneg, Rm, RM])
    _ = 2 * ρ[U ; μ # A] := by simp [rho]; ring
    _ ≤ 2 * r := by linarith
  refine ⟨t, ?_, ?_, ?_⟩
  · have : - r + (log (Nat.card A) + log ((H : Set G).ncard)) * (1 / 2 : ℝ) ≤
      log (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)) := by linarith
    have := exp_monotone this
    rwa [exp_add, exp_log (mod_cast hpos), exp_mul, exp_add,
      exp_log Hpos, exp_log Apos, mul_rpow, ← mul_assoc] at this <;> positivity
  · have : log (Nat.card A) ≤ 2 * r + log ((H : Set G).ncard) := by
      linarith [(abs_sub_le_iff.1 I).2]
    have := exp_monotone this
    rwa [exp_log Apos, exp_add, exp_log Hpos] at this
  · have : log ((H : Set G).ncard) ≤ 2 * r + log (Nat.card A) := by
      linarith [(abs_sub_le_iff.1 I).1]
    have := exp_monotone this
    rwa [exp_log Hpos, exp_add, exp_log Apos] at this

/-- If $H$ is a finite subgroup of $G$, and $\rho(U_H) \leq r$, then there exists $t$ such
that $|A \cap (H+t)| \geq e^{-r} \sqrt{|A||H|}$, and $|H|/|A| \in [e^{-2r}, e^{2r}]$. -/
lemma rho_of_submodule [IsProbabilityMeasure μ] [Module (ZMod 2) G]
    {H : Submodule (ZMod 2) G} {U : Ω → G}
    (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U)
    (r : ℝ) (hr : ρ[U ; μ # A] ≤ r) :
    ∃ t : G,
      exp (-r) * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (1 / 2 : ℝ) ≤
        Nat.card ↑(↑A ∩ (t +ᵥ (H : Set G)))
      ∧ Nat.card A ≤ exp (2 * r) * (H : Set G).ncard
      ∧ (H : Set G).ncard ≤ exp (2 * r) * Nat.card A :=
  rho_of_subgroup (H := H.toAddSubgroup) hunif hA hU r hr

/-- \rho(X)$ depends continuously on the distribution of $X$. -/
lemma rho_continuous [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    {A : Finset G} (hA : A.Nonempty) :
    Continuous fun μ : ProbabilityMeasure G ↦ ρ[(id : G → G) ; μ # A] :=
  ((rhoMinus_continuous hA).add (rhoPlus_continuous hA)).div_const _

lemma tendsto_rho_probabilityMeasure {α : Type*} {l : Filter α}
    [TopologicalSpace Ω] [BorelSpace Ω] [TopologicalSpace G] [BorelSpace G]
    [DiscreteTopology G] {X : Ω → G} (hX : Continuous X) (hA : A.Nonempty)
    {μ : α → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω} (hμ : Tendsto μ l (𝓝 ν)) :
    Tendsto (fun n ↦ ρ[X ; (μ n : Measure Ω) # A]) l (𝓝 (ρ[X ; ν # A])) := by
  have J (η : ProbabilityMeasure Ω) :
      ρ[X ; η # A] = ρ[(id : G → G) ; η.map hX.aemeasurable # A] := by
    apply rho_eq_of_identDistrib
    exact ⟨hX.aemeasurable, aemeasurable_id, by simp⟩
  simp_rw [J]
  have Z := ((rho_continuous hA).tendsto ((ν.map hX.aemeasurable)))
  have T : Tendsto (fun n ↦ (μ n).map hX.aemeasurable) l (𝓝 (ν.map hX.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hμ hX
  apply Z.comp T

/-- If $X,Y$ are independent, one has
  $$ \rho^-(X+Y) \leq \rho^-(X)$$ -/
lemma rhoMinus_of_sum [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y)
    (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    ρ⁻[X + Y ; μ # A] ≤ ρ⁻[X ; μ # A] := by
  rcases eq_zero_or_isProbabilityMeasure μ with hμ | hμ
  · simp [rhoMinus_zero_measure hμ]
  apply le_csInf (nonempty_rhoMinusSet hA)
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  rintro - ⟨μ', μ'_prob, habs, rfl⟩
  obtain ⟨Ω', hΩ', m, X', Y', T, U, hm, h_indep', hX', hY', hT, hU, hXX', hYY', hTμ, hU_unif⟩ :=
    independent_copies4_nondep (X₁ := X) (X₂ := Y) (X₃ := id) (X₄ := id) hX hY measurable_id
    measurable_id μ μ μ' (uniformOn (A : Set G))
  let _ : MeasureSpace Ω' := ⟨m⟩
  have hP : (ℙ : Measure Ω') = m := rfl
  have hTU : IdentDistrib (T + U) (Prod.fst + Prod.snd) ℙ (μ'.prod (uniformOn (A : Set G))) := by
    apply IdentDistrib.add
    · exact hTμ.trans IdentDistrib.fst_id.symm
    · exact hU_unif.trans IdentDistrib.snd_id.symm
    · exact h_indep'.indepFun (i := 2) (j := 3) (by simp)
    · exact indepFun_fst_snd
  have hXY : IdentDistrib (X + Y) (X' + Y') μ ℙ := by
    apply IdentDistrib.add hXX'.symm hYY'.symm h_indep
    exact h_indep'.indepFun zero_ne_one
  have hX'TUY' : IndepFun (⟨X', T + U⟩) Y' ℙ := by
    have I : iIndepFun ![X', Y', T + U] m :=
      ProbabilityTheory.iIndepFun.apply_two_last h_indep' hX' hY' hT hU
        (phi := fun a b ↦ a + b) (by fun_prop)
    exact (I.reindex_three_bac.pair_last_of_three hY' hX' (by fun_prop)).symm
  have I₁ : ρ⁻[X + Y ; μ # A] ≤ KL[X + Y ; μ # (T + Y') + U ; ℙ] := by
    apply rhoMinus_le (by fun_prop) hA _ (by fun_prop) (by fun_prop)
    · have : iIndepFun ![U, X', T, Y'] := h_indep'.reindex_four_dacb
      have : iIndepFun ![U, X', T + Y'] :=
        this.apply_two_last (phi := fun a b ↦ a + b) hU hX' hT hY' (by fun_prop)
      apply this.indepFun (i := 2) (j := 0)
      simp
    · rw [hXY.map_eq]
      have : T + Y' + U = (T + U) + Y' := by abel
      rw [this]
      apply absolutelyContinuous_add_of_indep hX'TUY' hX' (by fun_prop) hY'
      rw [hTU.map_eq, hP, hXX'.map_eq]
      exact habs
    · exact isUniform_uniformOn.of_identDistrib hU_unif.symm A.measurableSet
  have I₂ : KL[X + Y ; μ # (T + Y') + U ; ℙ] = KL[X' + Y' # (T + U) + Y'] := by
    apply IdentDistrib.KLDiv_eq _ _ hXY
    have : T + Y' + U = T + U + Y' := by abel
    rw [this]
    exact .refl <| by fun_prop
  have I₃ : KL[X' + Y' # (T + U) + Y'] ≤ KL[X' # T + U] := by
    apply KLDiv_add_le_KLDiv_of_indep _ (by fun_prop) (by fun_prop) (by fun_prop)
    · rw [hTU.map_eq, hP, hXX'.map_eq]
      exact habs
    · exact hX'TUY'
  have I₄ : KL[X' # T + U] = KL[X ; μ # Prod.fst + Prod.snd ; μ'.prod (uniformOn (A : Set G))] :=
    IdentDistrib.KLDiv_eq _ _ hXX' hTU
  exact ((I₁.trans_eq I₂).trans I₃).trans_eq I₄

/-- If $X,Y$ are independent, one has
$$ \rho^+(X+Y) \leq \rho^+(X) + \bbH[X+Y] - \bbH[X]$$ -/
lemma rhoPlus_of_sum [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    ρ⁺[X + Y ; μ # A] ≤ ρ⁺[X ; μ # A] + H[X + Y ; μ] - H[X ; μ] := by
  simp [rhoPlus]
  have := rhoMinus_of_sum hX hY hA h_indep
  linarith

/-- If $X,Y$ are independent, one has
$$\rho(X+Y) \leq \rho(X) + \frac{1}{2}( \bbH[X+Y] - \bbH[X]).$$ -/
lemma rho_of_sum [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    ρ[X + Y ; μ # A] ≤ ρ[X ; μ # A] + (H[X+Y ; μ] - H[X ; μ])/2 := by
  simp [rho, rhoPlus]
  have := rhoMinus_of_sum hX hY hA h_indep
  linarith

private lemma rho_le_translate [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hA : A.Nonempty) (s : G) :
    ρ[(fun ω ↦ X ω + s) ; μ # A] ≤ ρ[X ; μ # A] := by
  have : ρ[(fun ω ↦ X ω + s) ; μ # A] ≤ ρ[X ; μ # A] + (H[fun ω ↦ X ω + s ; μ] - H[X ; μ]) / 2 :=
    rho_of_sum (Y := fun ω ↦ s) hX measurable_const hA (indepFun_const s)
  have : H[fun ω ↦ X ω + s ; μ] = H[X ; μ] := entropy_add_const hX _
  linarith

lemma rho_of_translate [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hA : A.Nonempty) (s : G) :
    ρ[(fun ω ↦ X ω + s) ; μ # A] = ρ[X ; μ # A] := by
  apply le_antisymm (rho_le_translate hX hA s)
  convert rho_le_translate (X := fun ω ↦ X ω + s) (by fun_prop) hA (-s) (μ := μ) with ω
  abel

-- This may not be the optimal spelling for condRho, feel free to improve
/-- We define $\rho(X|Y) := \sum_y {\bf P}(Y=y) \rho(X|Y=y)$. -/
noncomputable def condRho {S : Type*}
    (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω) : ℝ :=
  ∑' s, μ.real (Y ⁻¹' {s}) * ρ[X ; μ[|Y ← s] # A]

/-- Average of rhoMinus along the fibers. -/
noncomputable def condRhoMinus {S : Type*}
    (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω) : ℝ :=
  ∑' s, μ.real (Y ⁻¹' {s}) * ρ⁻[X ; μ[|Y ← s] # A]

/-- Average of rhoPlus along the fibers. -/
noncomputable def condRhoPlus {S : Type*}
    (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω) : ℝ :=
  ∑' s, μ.real (Y ⁻¹' {s}) * ρ⁺[X ; μ[|Y ← s] # A]

@[inherit_doc condRho]
notation3:max "ρ[" X " | " Z " ; " μ " # " A "]" => condRho X Z A μ

@[inherit_doc condRho]
notation3:max "ρ[" X " | " Z " # " A "]" => condRho X Z A volume

@[inherit_doc condRhoMinus]
notation3:max "ρ⁻[" X " | " Z " ; " μ " # " A "]" => condRhoMinus X Z A μ

@[inherit_doc condRhoPlus]
notation3:max "ρ⁺[" X " | " Z " ; " μ " # " A "]" => condRhoPlus X Z A μ

/-- For any $s\in G$, $\rho(X+s|Y)=\rho(X|Y)$. -/
lemma condRho_of_translate {S : Type*}
    {Y : Ω → S} (hX : Measurable X) (hA : A.Nonempty) (s : G) :
    ρ[fun ω ↦ X ω + s | Y ; μ # A] = ρ[X | Y ; μ # A] := by
  simp [condRho, rho_of_translate hX hA]

omit [Finite G] [DiscreteMeasurableSpace G] in
variable (X) in
/-- If $f$ is injective, then $\rho(X|f(Y))=\rho(X|Y)$. -/
lemma condRho_of_injective {S T : Type*}
    (Y : Ω → S) {A : Finset G} {f : S → T} (hf : Function.Injective f) :
    ρ[X | f ∘ Y ; μ # A] = ρ[X | Y ; μ # A] := by
  simp only [condRho]
  rw [← hf.tsum_eq]
  · have I c : f ∘ Y ⁻¹' {f c} = Y ⁻¹' {c} := by
      ext z; simp [hf.eq_iff]
    simp [I]
  · intro y hy
    have : f ∘ Y ⁻¹' {y} ≠ ∅ := by
      intro h
      simp [h] at hy
    rcases Set.nonempty_iff_ne_empty.2 this with ⟨a, ha⟩
    simp only [mem_preimage, Function.comp_apply, mem_singleton_iff] at ha
    rw [← ha]
    exact mem_range_self (Y a)

lemma condRho_eq_of_identDistrib {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    {Y : Ω → G} {W : Ω → S} {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {Y' : Ω' → G} {W' : Ω' → S} (hY : Measurable Y) (hW : Measurable W) (hY' : Measurable Y')
    (hW' : Measurable W')
    (h : IdentDistrib (⟨Y, W⟩) (⟨Y', W'⟩) μ μ') :
    ρ[Y | W ; μ # A] = ρ[Y' | W' ; μ' # A] := by
  rw [condRho]
  congr with g
  have M : μ (W ⁻¹' {g}) = μ' (W' ⁻¹' {g}) := by
    have I : IdentDistrib W W' μ μ' := h.comp (u := Prod.snd) measurable_snd
    rw [← map_apply hW (.singleton _), ← map_apply hW' (.singleton _), I.map_eq]
  have M' : μ.real (W ⁻¹' {g}) = μ'.real (W' ⁻¹' {g}) := by simp [measureReal_def, M]
  rw [M']
  congr 1
  apply rho_eq_of_identDistrib
  refine ⟨hY.aemeasurable, hY'.aemeasurable, ?_⟩
  ext s hs
  rw [map_apply hY hs, map_apply hY' hs, cond_apply (hW (.singleton _)),
    cond_apply (hW' (.singleton _)), M]
  congr
  have E : W ⁻¹' {g} ∩ Y ⁻¹' s = (⟨Y, W⟩) ⁻¹' (s ×ˢ {g}) := by ext; aesop
  have F : W' ⁻¹' {g} ∩ Y' ⁻¹' s = (⟨Y', W'⟩) ⁻¹' (s ×ˢ {g}) := by ext; aesop
  rw [E, F, ← map_apply (by fun_prop) (hs.prod (.singleton _)),
    ← map_apply (by fun_prop) (hs.prod (.singleton _)), h.map_eq]

/-- $$ \rho^-(X|Z) \leq \rho^-(X) + \bbH[X] - \bbH[X|Z]$$ -/
lemma condRhoMinus_le [IsZeroOrProbabilityMeasure μ] {S : Type*} [MeasurableSpace S]
    [Finite S] [MeasurableSingletonClass S]
    {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z) (hA : A.Nonempty) :
    ρ⁻[X | Z ; μ # A] ≤ ρ⁻[X ; μ # A] + H[X ; μ] - H[X | Z ; μ] := by
  cases nonempty_fintype S
  have : IsProbabilityMeasure (uniformOn (A : Set G)) := by
    apply isProbabilityMeasure_uniformOn A.finite_toSet hA
  suffices ρ⁻[X | Z ; μ # A] - H[X ; μ] + H[X | Z ; μ] ≤ ρ⁻[X ; μ # A] by linarith
  apply le_csInf (nonempty_rhoMinusSet hA)
  rintro - ⟨μ', hμ', habs, rfl⟩
  rw [condRhoMinus, tsum_fintype]
  let _ : MeasureSpace (G × G) := ⟨μ'.prod (uniformOn (A : Set G))⟩
  have hP : (ℙ : Measure (G × G)) = μ'.prod (uniformOn (A : Set G)) := rfl
  have : IsProbabilityMeasure (ℙ : Measure (G × G)) := by rw [hP]; infer_instance
  have : ∑ b : S, μ.real (Z ⁻¹' {b}) * ρ⁻[X ; μ[|Z ← b] # A]
      ≤ KL[ X | Z ; μ # (Prod.fst + Prod.snd : G × G → G) ; ℙ] := by
    rw [condKLDiv, tsum_fintype]
    apply Finset.sum_le_sum (fun i hi ↦ ?_)
    gcongr
    apply rhoMinus_le_def hX (fun y hy ↦ ?_)
    have T := habs y hy
    rw [Measure.map_apply hX (measurableSet_singleton _)] at T ⊢
    exact cond_absolutelyContinuous T
  rw [condKLDiv_eq hX hZ (by exact habs)] at this
  rw [← hP]
  linarith

/-- $$ \rho^+(X|Z) \leq \rho^+(X)$$ -/
lemma condRhoPlus_le [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S]
    [Finite S] [MeasurableSingletonClass S]
    {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z) (hA : A.Nonempty) :
    ρ⁺[X | Z ; μ # A] ≤ ρ⁺[X ; μ # A] := by
  cases nonempty_fintype S
  have : IsProbabilityMeasure (Measure.map Z μ) := isProbabilityMeasure_map hZ.aemeasurable
  have I₁ := condRhoMinus_le hX hZ hA (μ := μ)
  simp_rw [condRhoPlus, rhoPlus, tsum_fintype]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, tsub_le_iff_right]
  rw [← Finset.sum_mul, ← tsum_fintype (L := SummationFilter.unconditional _),
    ← condRhoMinus, ← condEntropy_eq_sum_fintype _ _ _ hZ]
  simp_rw [← map_measureReal_apply hZ (measurableSet_singleton _)]
  simp only [sum_measureReal_singleton, Finset.coe_univ, probReal_univ, one_mul,
    sub_add_cancel, ge_iff_le]
  linarith

omit [Finite G] [DiscreteMeasurableSpace G] in
lemma condRho_eq {S : Type*} [Finite S] {Z : Ω → S} :
    ρ[X | Z ; μ # A] = (ρ⁻[X | Z ; μ # A] + ρ⁺[X | Z ; μ # A]) / 2 := by
  cases nonempty_fintype S
  simp_rw [condRho, rho, ← mul_div_assoc, tsum_fintype, ← Finset.sum_div, mul_add,
    Finset.sum_add_distrib, ← tsum_fintype (L := SummationFilter.unconditional _)]
  rfl

/-- $$ \rho(X|Z) \leq \rho(X) + \frac{1}{2}( \bbH[X] - \bbH[X|Z])$$ -/
lemma condRho_le [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S]
    [Finite S] [MeasurableSingletonClass S]
    {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z) (hA : A.Nonempty) :
    ρ[X | Z ; μ # A] ≤ ρ[X ; μ # A] + (H[X ; μ] - H[X | Z ; μ]) / 2 := by
  rw [condRho_eq, rho]
  linarith [condRhoMinus_le hX hZ hA (μ := μ), condRhoPlus_le hX hZ hA (μ := μ)]

omit [Finite G] [DiscreteMeasurableSpace G] in
lemma condRho_prod_eq_sum [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S]
    [Fintype S] [MeasurableSingletonClass S]
    {Z T : Ω → S} (hZ : Measurable Z) (hT : Measurable T) :
    ρ[X | ⟨Z, T⟩ ; μ # A] = ∑ g, μ.real (T ⁻¹' {g}) * ρ[X | Z ; μ[|T ← g] # A] := by
  rw [condRho, tsum_fintype, ← Finset.univ_product_univ, Finset.sum_product_right]
  congr 1 with w
  simp only [condRho, tsum_fintype, Finset.mul_sum]
  congr 1 with w'
  rw [← mul_assoc]
  have A : (fun a ↦ (Z a, T a)) ⁻¹' {(w', w)} = Z ⁻¹' {w'} ∩ T ⁻¹' {w} := by ext; simp
  congr 1
  · simp only [A, ProbabilityTheory.cond]
    rcases le_or_gt (μ.real (T ⁻¹' {w})) 0 with hw|hw
    · have : μ.real (Z ⁻¹' {w'} ∩ T ⁻¹' {w}) = 0 :=
        le_antisymm (le_trans (measureReal_mono Set.inter_subset_right) hw) measureReal_nonneg
      have hw' : μ.real (T ⁻¹' {w}) = 0 := le_antisymm hw measureReal_nonneg
      simp [hw', this]
    · simp only [measureReal_ennreal_smul_apply, ENNReal.toReal_inv]
      rw [← mul_assoc, ← measureReal_def, mul_inv_cancel₀ hw.ne', one_mul]
      rw [measureReal_def, measureReal_def, Measure.restrict_apply]
      exact hZ (measurableSet_singleton w')
  · congr 1
    rw [A, cond_cond_eq_cond_inter' (hT (.singleton _)) (hZ (.singleton _)), Set.inter_comm]
    finiteness

/-- $$ \rho(X|Z) \leq \rho(X) + \frac{1}{2}( \bbH[X] - \bbH[X|Z])$$, conditional version -/
lemma condRho_prod_le [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S]
    [Finite S] [MeasurableSingletonClass S]
    {Z T : Ω → S} (hX : Measurable X) (hZ : Measurable Z) (hT : Measurable T) (hA : A.Nonempty) :
    ρ[X | ⟨Z, T⟩ ; μ # A] ≤ ρ[X | T ; μ # A] + (H[X | T ; μ] - H[X | ⟨Z, T⟩ ; μ]) / 2 := by
  cases nonempty_fintype S
  rw [condRho_prod_eq_sum hZ hT]
  have : ∑ g : S, μ.real (T ⁻¹' {g}) * ρ[ X | Z ; μ[|T ⁻¹' {g}] # A] ≤
    ∑ g : S, μ.real (T ⁻¹' {g}) *
      (ρ[X ; μ[|T ⁻¹' {g}] # A] + (H[X ; μ[|T ⁻¹' {g}]] - H[X | Z ; μ[|T ⁻¹' {g}]]) / 2) := by
    apply Finset.sum_le_sum (fun g hg ↦ ?_)
    rcases eq_or_ne (μ.real (T ⁻¹' {g})) 0 with hpg | hpg
    · simp [hpg]
    gcongr
    have hμ : IsProbabilityMeasure (μ[|T ⁻¹' {g}]) := cond_isProbabilityMeasure_of_real hpg
    exact condRho_le hX hZ hA
  apply this.trans_eq
  simp_rw [mul_add, mul_div, mul_sub, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_sub_distrib, condRho, tsum_fintype, condEntropy_eq_sum_fintype X T μ hT,
    condEntropy_prod_eq_sum μ hZ hT]

lemma condRho_prod_eq_of_indepFun [IsProbabilityMeasure μ]
    {X : Ω → G} {S : Type*} [Finite S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {W W' : Ω → S} (hX : Measurable X) (hW : Measurable W)
    (hW' : Measurable W') (h : IndepFun (⟨X, W⟩) W' μ) :
    ρ[X | ⟨W, W'⟩ ; μ # A] = ρ[X | W ; μ # A] := by
  cases nonempty_fintype S
  rw [condRho_prod_eq_sum hW hW']
  have : ρ[X | W ; μ # A] = ∑ z, μ.real (W' ⁻¹' {z}) * ρ[X | W ; μ # A] := by
    rw [← Finset.sum_mul, sum_measureReal_preimage_singleton]
    · simp
    · exact fun y hy ↦ hW' (measurableSet_singleton y)
  rw [this]
  congr with w
  rcases eq_or_ne (μ.real (W' ⁻¹' {w})) 0 with hw|hw
  · simp [hw]
  congr 1
  apply condRho_eq_of_identDistrib hX hW hX hW
  simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at hw
  exact (h.identDistrib_cond (MeasurableSet.singleton w) (by fun_prop) hW' hw).symm

variable [Module (ZMod 2) G]

/-- If $X,Y$ are independent, then
  $$ \rho(X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$ -/
lemma rho_of_sum_le [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    ρ[X + Y ; μ # A] ≤ (ρ[X ; μ # A] + ρ[Y ; μ # A] + d[ X ; μ # Y ; μ]) / 2 := by
  have I : ρ[X + Y ; μ # A] ≤ ρ[X ; μ # A] + (H[X+Y ; μ] - H[X ; μ])/2 :=
    rho_of_sum hX hY hA h_indep
  have J : ρ[Y + X ; μ # A] ≤ ρ[Y ; μ # A] + (H[Y+X ; μ] - H[Y ; μ ])/2 :=
    rho_of_sum hY hX hA h_indep.symm
  have : Y + X = X + Y := by abel
  rw [this] at J
  have : X - Y = X + Y := ZModModule.sub_eq_add _ _
  rw [h_indep.rdist_eq hX hY, sub_eq_add_neg, this]
  linarith

/-- If $X,Y$ are independent, then
  $$ \rho(X | X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$ -/
lemma condRho_of_sum_le [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hA : A.Nonempty) (h_indep : IndepFun X Y μ) :
    ρ[X | X + Y ; μ # A] ≤ (ρ[X ; μ # A] + ρ[Y ; μ # A] + d[ X ; μ # Y ; μ ]) / 2 := by
  have I : ρ[X | X + Y ; μ # A] ≤ ρ[X ; μ # A] + (H[X ; μ] - H[X | X + Y ; μ]) / 2 :=
    condRho_le hX (by fun_prop) hA
  have I' : H[X ; μ] - H[X | X + Y ; μ] = H[X + Y ; μ] - H[Y ; μ] := by
    rw [ProbabilityTheory.chain_rule'' _ hX (by fun_prop), entropy_add_right hX hY,
      IndepFun.entropy_pair_eq_add hX hY h_indep]
    abel
  have J : ρ[Y | Y + X ; μ # A] ≤ ρ[Y ; μ # A] + (H[Y ; μ] - H[Y | Y + X ; μ]) / 2 :=
    condRho_le hY (by fun_prop) hA
  have J' : H[Y ; μ] - H[Y | Y + X ; μ] = H[Y + X ; μ] - H[X ; μ] := by
    rw [ProbabilityTheory.chain_rule'' _ hY (by fun_prop), entropy_add_right hY hX,
      IndepFun.entropy_pair_eq_add hY hX h_indep.symm]
    abel
  have : Y + X = X + Y := by abel
  simp only [this] at J J'
  have : ρ[X | X + Y ; μ # A] = ρ[Y | X + Y ; μ # A] := by
    simp only [condRho]
    congr with s
    congr 1
    have : ρ[X ; μ[|(X + Y) ⁻¹' {s}] # A] = ρ[fun ω ↦ X ω + s ; μ[|(X + Y) ⁻¹' {s}] # A] := by
      rw [rho_of_translate hX hA]
    rw [this]
    apply rho_eq_of_identDistrib
    apply IdentDistrib.of_ae_eq (by fun_prop)
    have : MeasurableSet ((X + Y) ⁻¹' {s}) := by
      have : Measurable (X + Y) := by fun_prop
      exact this (measurableSet_singleton _)
    filter_upwards [ae_cond_mem this] with a ha
    simp only [mem_preimage, Pi.add_apply, mem_singleton_iff] at ha
    rw [← ha]
    nth_rewrite 1 [← ZModModule.neg_eq_self (X a)]
    abel
  have : X - Y = X + Y := ZModModule.sub_eq_add _ _
  rw [h_indep.rdist_eq hX hY, sub_eq_add_neg, this]
  linarith

end

section phiMinimizer

variable {G : Type uG} [AddCommGroup G] [Finite G] [hGm : MeasurableSpace G]
[DiscreteMeasurableSpace G] {Ω : Type*} [MeasureSpace Ω]
{X Y Z : Ω → G} {A : Finset G}

/-- Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$. -/
noncomputable def phi {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → G) (η : ℝ) (A : Finset G) (μ : Measure Ω) : ℝ :=
  d[ X ; μ # Y ; μ] + η * (ρ[X ; μ # A] + ρ[Y ; μ # A])

/-- Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$
and define a \emph{$\phi$-minimizer} to be a pair of random variables $X,Y$ which
minimizes $\phi[X;Y]$. -/
def phiMinimizes {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → G) (η : ℝ) (A : Finset G)
    (μ : Measure Ω) : Prop :=
  ∀ (Ω' : Type uG) (_ : MeasureSpace Ω') (X' Y' : Ω' → G),
    IsProbabilityMeasure (ℙ : Measure Ω') → Measurable X' → Measurable Y' →
    phi X Y η A μ ≤ phi X' Y' η A ℙ

lemma phiMinimizes_of_identDistrib {Ω' : Type*} [MeasureSpace Ω']
    {X Y : Ω → G} {X' Y' : Ω' → G} {η : ℝ} {A : Finset G}
    (h_min : phiMinimizes X Y η A ℙ) (h₁ : IdentDistrib X X') (h₂ : IdentDistrib Y Y') :
    phiMinimizes X' Y' η A ℙ := by
  have : phi X Y η A ℙ = phi X' Y' η A ℙ := by
    simp only [phi]
    rw [h₁.rdist_congr h₂, rho_eq_of_identDistrib h₁, rho_eq_of_identDistrib h₂]
  simpa [phiMinimizes, this] using h_min

lemma phiMinimizes_comm [IsProbabilityMeasure (ℙ : Measure Ω)] {X Y : Ω → G} {η : ℝ} {A : Finset G}
    (h_min : phiMinimizes X Y η A ℙ) : phiMinimizes Y X η A ℙ := by
  have : phi Y X η A ℙ = phi X Y η A ℙ := by
    simp only [phi]
    rw [rdist_symm]
    linarith
  simpa [phiMinimizes, this] using h_min

variable {η : ℝ} (hη : 0 < η)

/-- There exists a $\phi$-minimizer. -/
lemma phi_min_exists (hA : A.Nonempty) : ∃ (μ : Measure (G × G)), IsProbabilityMeasure μ ∧
    phiMinimizes Prod.fst Prod.snd η A μ := by
  let _i : TopologicalSpace G := (⊥ : TopologicalSpace G)
  have : DiscreteTopology G := ⟨rfl⟩
  let iG : Inhabited G := ⟨0⟩
  have T : Continuous (fun (μ : ProbabilityMeasure (G × G)) ↦ phi Prod.fst Prod.snd η A μ) := by
    apply continuous_iff_continuousAt.2 (fun μ ↦ ?_)
    apply Tendsto.add
    · apply tendsto_rdist_probabilityMeasure continuous_fst continuous_snd tendsto_id
    apply Tendsto.const_mul
    apply Tendsto.add
    · apply tendsto_rho_probabilityMeasure continuous_fst hA tendsto_id
    · apply tendsto_rho_probabilityMeasure continuous_snd hA tendsto_id
  obtain ⟨μ, _, hμ⟩ := @IsCompact.exists_isMinOn ℝ (ProbabilityMeasure (G × G))
                          _ _ _ _ Set.univ isCompact_univ ⟨default, trivial⟩ _ T.continuousOn
  refine ⟨μ, by infer_instance, ?_⟩
  intro Ω' mΩ' X' Y' hP hX' hY'
  let ν : Measure (G × G) := Measure.map (⟨X', Y'⟩) ℙ
  have : IsProbabilityMeasure ν := isProbabilityMeasure_map (by fun_prop)
  let ν' : ProbabilityMeasure (G × G) := ⟨ν, this⟩
  have : phi Prod.fst Prod.snd η A ↑μ ≤ phi Prod.fst Prod.snd η A ↑ν' := hμ (mem_univ _)
  apply this.trans_eq
  have h₁ : IdentDistrib Prod.fst X' (ν' : Measure (G × G)) ℙ := by
    refine ⟨measurable_fst.aemeasurable, hX'.aemeasurable, ?_⟩
    simp only [ProbabilityMeasure.coe_mk, ν', ν]
    rw [Measure.map_map measurable_fst (by fun_prop)]
    rfl
  have h₂ : IdentDistrib Prod.snd Y' (ν' : Measure (G × G)) ℙ := by
    refine ⟨measurable_snd.aemeasurable, hY'.aemeasurable, ?_⟩
    simp only [ProbabilityMeasure.coe_mk, ν', ν]
    rw [Measure.map_map measurable_snd (by fun_prop)]
    rfl
  simp [phi, h₁.rdist_congr h₂, rho_eq_of_identDistrib h₁, rho_eq_of_identDistrib h₂]

-- Let $(X_1, X_2)$ be a $\phi$-minimizer, and $\tilde X_1, \tilde X_2$ be independent copies
-- of $X_1,X_2$ respectively.
variable {X₁ X₂ X₁' X₂' : Ω → G} (h_min : phiMinimizes X₁ X₂ η A ℙ)
  (h₁ : IdentDistrib X₁ X₁')
  (h₂ : IdentDistrib X₂ X₂')
  (h_indep : iIndepFun ![X₁, X₂, X₁', X₂'])
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']
local notation3 "I₂" => I[X₁ + X₂ : X₁ + X₁' | X₁ + X₂ + X₁' + X₂']
/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[X₁ # X₂]

lemma le_rdist_of_phiMinimizes (h_min : phiMinimizes X₁ X₂ η A ℙ)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X₁' : Ω₁ → G} {X₂' : Ω₂ → G} (hX₁' : Measurable X₁') (hX₂' : Measurable X₂') :
    d[X₁ # X₂] - η * (ρ[X₁' ; μ₁ # A] - ρ[X₁ # A]) - η * (ρ[X₂' ; μ₂ # A] - ρ[X₂ # A])
      ≤ d[X₁' ; μ₁ # X₂' ; μ₂] := by
  let Ω' : Type uG := G × G
  have : IsProbabilityMeasure (Measure.map X₁' μ₁) := isProbabilityMeasure_map hX₁'.aemeasurable
  have : IsProbabilityMeasure (Measure.map X₂' μ₂) := isProbabilityMeasure_map hX₂'.aemeasurable
  let m : Measure Ω' := (Measure.map X₁' μ₁).prod (Measure.map X₂' μ₂)
  have m_prob : IsProbabilityMeasure m := by infer_instance
  let _ : MeasureSpace Ω' := ⟨m⟩
  have hP : (ℙ : Measure Ω') = m := rfl
  let Y₁ : G × G → G := Prod.fst
  let Y₂ : G × G → G := Prod.snd
  have : phi X₁ X₂ η A ℙ ≤ phi Y₁ Y₂ η A ℙ := h_min _ _ _ _ m_prob measurable_fst measurable_snd
  have Id₁ : IdentDistrib Y₁ X₁' ℙ μ₁ :=
    ⟨measurable_fst.aemeasurable, hX₁'.aemeasurable, by simp [Y₁, hP, m]⟩
  have Id₂ : IdentDistrib Y₂ X₂' ℙ μ₂ :=
    ⟨measurable_snd.aemeasurable, hX₂'.aemeasurable, by simp [Y₂, hP, m]⟩
  have I : d[Y₁ # Y₂] = d[X₁' ; μ₁ # X₂' ; μ₂] := Id₁.rdist_congr Id₂
  have J : ρ[Y₁ # A] = ρ[X₁' ; μ₁ # A] := rho_eq_of_identDistrib Id₁
  have K : ρ[Y₂ # A] = ρ[X₂' ; μ₂ # A] := rho_eq_of_identDistrib Id₂
  simp only [phi, I, J, K] at this
  linarith

lemma le_rdist_of_phiMinimizes' (h_min : phiMinimizes X₁ X₂ η A ℙ)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X₁' : Ω₁ → G} {X₂' : Ω₂ → G} (hX₁' : Measurable X₁') (hX₂' : Measurable X₂') :
    d[X₁ # X₂] ≤ d[X₁' ; μ₁ # X₂' ; μ₂] +
      η * (ρ[X₁' ; μ₁ # A] - ρ[X₁ # A]) + η * (ρ[X₂' ; μ₂ # A] - ρ[X₂ # A]) := by
  linarith [le_rdist_of_phiMinimizes h_min hX₁' hX₂' (μ₁ := μ₁) (μ₂ := μ₂)]

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

lemma condRho_le_condRuzsaDist_of_phiMinimizes {S T : Type*}
    [Finite S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Finite T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (h : phiMinimizes X₁ X₂ η A ℙ) (h1 : Measurable X₁') (h2 : Measurable X₂')
    {Z : Ω → S} {W : Ω → T} (hZ : Measurable Z) (hW : Measurable W) :
    k - η * (ρ[X₁' | Z # A] - ρ[X₁ # A]) - η * (ρ[X₂' | W # A] - ρ[X₂ # A])
      ≤ d[X₁' | Z # X₂' | W] := by
  cases nonempty_fintype S
  cases nonempty_fintype T
  have : IsProbabilityMeasure (Measure.map Z ℙ) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (Measure.map W ℙ) := isProbabilityMeasure_map hW.aemeasurable
  have hz (a : ℝ) : a = ∑ z, (Measure.real ℙ (Z ⁻¹' {z})) * a := by
    simp_rw [← Finset.sum_mul, ← map_measureReal_apply hZ (MeasurableSet.singleton _),
      sum_measureReal_singleton]
    simp
  have hw (a : ℝ) : a = ∑ w, (Measure.real ℙ (W ⁻¹' {w})) * a := by
    simp_rw [← Finset.sum_mul, ← map_measureReal_apply hW (MeasurableSet.singleton _),
      sum_measureReal_singleton]
    simp
  rw [condRuzsaDist_eq_sum' h1 hZ h2 hW, hz d[X₁ # X₂],
    hz (ρ[X₁ # A]), hz (η * (ρ[X₂' | W # A] - ρ[X₂ # A])), condRho, tsum_fintype,
    ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro z _
  rw [condRho, tsum_fintype, hw ρ[X₂ # A],
    hw ( (Measure.real ℙ (Z ⁻¹' {z})) * k -
    η * ((Measure.real ℙ (Z ⁻¹' {z})) * ρ[X₁' ; ℙ[|Z ⁻¹' {z}] # A]
      - (Measure.real ℙ (Z ⁻¹' {z})) * ρ[X₁ # A])),
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro w _
  rcases eq_or_ne (Measure.real ℙ (Z ⁻¹' {z})) 0 with hpz | hpz
  · simp [hpz]
  rcases eq_or_ne (Measure.real ℙ (W ⁻¹' {w})) 0 with hpw | hpw
  · simp [hpw]
  set μ := ℙ[|Z ← z]
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_real hpz
  set μ' := ℙ[|W ← w]
  have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure_of_real hpw
  suffices d[X₁ # X₂] - η * (ρ[X₁' ; μ # A] - ρ[X₁ # A]) -
      η * (ρ[X₂' ; μ' # A] - ρ[X₂ # A]) ≤ d[X₁' ; μ # X₂'; μ'] by
    replace this := mul_le_mul_of_nonneg_left this
      (show 0 ≤ (Measure.real ℙ (Z ⁻¹' {z})) * (Measure.real ℙ (W ⁻¹' {w})) by positivity)
    convert this using 1
    ring
  exact le_rdist_of_phiMinimizes h h1 h2


variable [Module (ZMod 2) G]

/- *****************************************
First estimate
********************************************* -/

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min hη in
/-- $I_1\le 2\eta d[X_1;X_2]$ -/
lemma I_one_le (hA : A.Nonempty) : I₁ ≤ 2 * η * d[ X₁ # X₂ ] := by
  have : d[X₁ + X₂' # X₂ + X₁'] + d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] + I₁ = 2 * k :=
    rdist_add_rdist_add_condMutual_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep.reindex_four_abdc
  have : k - η * (ρ[X₁ | X₁ + X₂' # A] - ρ[X₁ # A])
      - η * (ρ[X₂ | X₂ + X₁' # A] - ρ[X₂ # A]) ≤ d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] :=
    condRho_le_condRuzsaDist_of_phiMinimizes h_min hX₁ hX₂ (by fun_prop) (by fun_prop)
  have : k - η * (ρ[X₁ + X₂' # A] - ρ[X₁ # A])
      - η * (ρ[X₂ + X₁' # A] - ρ[X₂ # A]) ≤ d[X₁ + X₂' # X₂ + X₁'] :=
    le_rdist_of_phiMinimizes h_min (hX₁.add hX₂') (hX₂.add hX₁')
  have : ρ[X₁ + X₂' # A] ≤ (ρ[X₁ # A] + ρ[X₂ # A] + d[ X₁ # X₂ ]) / 2 := by
    rw [rho_eq_of_identDistrib h₂, h₂.rdist_congr_right hX₁.aemeasurable]
    apply rho_of_sum_le hX₁ hX₂' hA
    simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
  have : ρ[X₂ + X₁' # A] ≤ (ρ[X₁ # A] + ρ[X₂ # A] + d[ X₁ # X₂ ]) / 2 := by
    rw [add_comm, rho_eq_of_identDistrib h₁, h₁.rdist_congr_left hX₂.aemeasurable]
    apply rho_of_sum_le hX₁' hX₂ hA
    simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 1 by decide)
  have : ρ[X₁ | X₁ + X₂' # A] ≤ (ρ[X₁ # A] + ρ[X₂ # A] + d[ X₁ # X₂ ]) / 2 := by
    rw [rho_eq_of_identDistrib h₂, h₂.rdist_congr_right hX₁.aemeasurable]
    apply condRho_of_sum_le hX₁ hX₂' hA
    simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
  have : ρ[X₂ | X₂ + X₁' # A] ≤ (ρ[X₁ # A] + ρ[X₂ # A] + d[ X₁ # X₂ ]) / 2 := by
    have : ρ[X₂ | X₂ + X₁' # A] ≤ (ρ[X₂ # A] + ρ[X₁' # A] + d[ X₂ # X₁' ]) / 2 := by
      apply condRho_of_sum_le hX₂ hX₁' hA
      simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 2 by decide)
    have I : ρ[X₁' # A] = ρ[X₁ # A] := rho_eq_of_identDistrib h₁.symm
    have J : d[X₂ # X₁'] = d[X₁ # X₂] := by
      rw [rdist_symm, h₁.rdist_congr_left hX₂.aemeasurable]
    linarith
  nlinarith

/- *****************************************
Second estimate
********************************************* -/

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
lemma I_two_aux :
    d[X₁ # X₁] + d[X₂ # X₂] = d[X₁ + X₂' # X₂ + X₁'] + d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] + I₂ := by
  cases nonempty_fintype G
  have Z : d[X₁' # X₁] + d[X₂' # X₂] = d[X₁' + X₂' # X₁ + X₂] + d[X₁' | X₁' + X₂' # X₁ | X₁ + X₂]
      + I[X₁' + X₁ : X₁ + X₂|X₁' + X₁ + X₂' + X₂] :=
    sum_of_rdist_eq_char_2' X₁' X₁ X₂' X₂ h_indep.reindex_four_cadb hX₁' hX₁ hX₂' hX₂
  have C₁ : X₁' + X₁ + X₂' + X₂ = X₁ + X₂ + X₁' + X₂' := by abel
  have C₂ : X₁' + X₁ = X₁ + X₁' := by abel
  have C₃ : d[X₁' # X₁] = d[X₁ # X₁] := h₁.symm.rdist_congr_left hX₁.aemeasurable
  have C₄ : d[X₂' # X₂] = d[X₂ # X₂] := h₂.symm.rdist_congr_left hX₂.aemeasurable
  have C₅ : d[X₁' + X₂' # X₁ + X₂] = d[X₁ + X₂' # X₂ + X₁'] := by
    apply IdentDistrib.rdist_congr
    · apply h₁.symm.add (.refl hX₂'.aemeasurable)
      · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 3 by decide)
      · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
    · rw [add_comm]
      refine .add (.refl hX₂.aemeasurable) h₁ ?_ ?_
      · simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 0 by decide)
      · simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 2 by decide)
  have C₆ : d[X₁' | X₁' + X₂' # X₁ | X₁ + X₂] = d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] := by
    have A : d[X₁' | X₁' + X₂' # X₁ | X₁ + X₂] = d[X₁ | X₁ + X₂' # X₁' | X₂ + X₁'] := by
      apply condRuzsaDist_of_copy hX₁' (by fun_prop) hX₁ (by fun_prop) hX₁ (by fun_prop) hX₁'
        (by fun_prop)
      · have : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂'⟩) := by
          apply h₁.symm.prodMk (.refl hX₂'.aemeasurable)
          · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 3 by decide)
          · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
        exact this.comp (u := fun (a : G × G) ↦ (a.1, a.1 + a.2)) (by fun_prop)
      · rw [add_comm]
        have : IdentDistrib (⟨X₁, X₂⟩) (⟨X₁', X₂⟩) := by
          apply h₁.prodMk (.refl hX₂.aemeasurable)
          · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 1 by decide)
          · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 1 by decide)
        exact this.comp (u := fun (a : G × G) ↦ (a.1, a.2 + a.1)) (by fun_prop)
    have B : d[X₁ | X₁ + X₂' # X₁' | X₂ + X₁'] = d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] := by
      have J z w : d[X₁ ; ℙ[|(X₁ + X₂') ⁻¹' {z}] # X₁' ; ℙ[|(X₂ + X₁') ⁻¹' {w}]]
          = d[X₁ ; ℙ[|(X₁ + X₂') ⁻¹' {z}] # X₂ ; ℙ[|(X₂ + X₁') ⁻¹' {w}]] := by
        rw [← rdist_add_const hX₁ hX₂ (c := w)]
        apply (IdentDistrib.refl hX₁.aemeasurable).rdist_congr
        apply IdentDistrib.of_ae_eq hX₁'.aemeasurable
        filter_upwards [ae_cond_mem (hX₂.add hX₁' (measurableSet_singleton _))] with x hx
        simp only [mem_preimage, Pi.add_apply, mem_singleton_iff] at hx
        simp [← hx, ← add_assoc, ZModModule.add_self (X₂ x)]
      rw [condRuzsaDist_eq_sum' hX₁ (by fun_prop) hX₁' (by fun_prop),
        condRuzsaDist_eq_sum' hX₁ (by fun_prop) hX₂ (by fun_prop)]
      simp [J]
    exact A.trans B
  rwa [condMutualInfo_comm (by fun_prop) (by fun_prop), C₁, C₂, C₃, C₄, C₅, C₆] at Z

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
/-- $d[X_1;X_1]+d[X_2;X_2]= 2d[X_1;X_2]+(I_2-I_1)$. -/
lemma rdist_add_rdist_eq :
    d[ X₁ # X₁ ] + d[ X₂ # X₂ ] = 2 * k + (I₂ - I₁) := by
  have : d[X₁ + X₂' # X₂ + X₁'] + d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] + I₁ = 2 * k :=
    rdist_add_rdist_add_condMutual_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep.reindex_four_abdc
  have : d[X₁ # X₁] + d[X₂ # X₂]
      = d[X₁ + X₂' # X₂ + X₁'] + d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] + I₂ :=
    I_two_aux h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂'
  linarith

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
lemma I_two_aux' :
    2 * k = d[X₁ + X₁' # X₂ + X₂'] + d[X₁ | X₁ + X₁' # X₂ | X₂ + X₂'] + I₂ := by
  have Z : d[X₂ # X₁] + d[X₂' # X₁'] = d[X₂ + X₂' # X₁ + X₁'] + d[X₂ | X₂ + X₂' # X₁ | X₁ + X₁']
      + I[X₂ + X₁ : X₁ + X₁' | X₂ + X₁ + X₂' + X₁'] :=
    sum_of_rdist_eq_char_2' X₂ X₁ X₂' X₁' h_indep.reindex_four_badc hX₂ hX₁ hX₂' hX₁'
  have C₁ : X₂ + X₁ = X₁ + X₂ := by abel
  have C₂ : X₁ + X₂ + X₂' + X₁' = X₁ + X₂ + X₁' + X₂' := by abel
  have C₃ : d[X₂ # X₁] = d[X₁ # X₂] := rdist_symm
  have C₄ : d[X₂' # X₁'] = d[X₁ # X₂] := by rw [rdist_symm]; exact h₁.symm.rdist_congr h₂.symm
  have C₅ : d[X₂ + X₂' # X₁ + X₁'] = d[X₁ + X₁' # X₂ + X₂'] := rdist_symm
  have C₆ : d[X₂ | X₂ + X₂' # X₁ | X₁ + X₁'] = d[X₁ | X₁ + X₁' # X₂ | X₂ + X₂'] :=
    condRuzsaDist_symm (by fun_prop) (by fun_prop)
  rw [C₁, C₂, C₃, C₄, C₅] at Z
  linarith

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min hη in
/-- $I_2\le 2\eta d[X_1;X_2] + \frac{\eta}{1-\eta}(2\eta d[X_1;X_2]-I_1)$. -/
lemma I_two_le (hA : A.Nonempty) (h'η : η < 1) :
    I₂ ≤ 2 * η * k + (η / (1 - η)) * (2 * η * k - I₁) := by
  have W : k - η * (ρ[X₁ + X₁' # A] - ρ[X₁ # A]) - η * (ρ[X₂ + X₂' # A] - ρ[X₂ # A]) ≤
      d[X₁ + X₁' # X₂ + X₂'] :=
    le_rdist_of_phiMinimizes h_min (hX₁.add hX₁') (hX₂.add hX₂') (μ₁ := ℙ) (μ₂ := ℙ)
  have W' : k - η * (ρ[X₁ | X₁ + X₁' # A] - ρ[X₁ # A])
      - η * (ρ[X₂ | X₂ + X₂' # A] - ρ[X₂ # A]) ≤ d[X₁ | X₁ + X₁' # X₂ | X₂ + X₂'] :=
    condRho_le_condRuzsaDist_of_phiMinimizes h_min hX₁ hX₂ (hX₁.add hX₁') (hX₂.add hX₂')
  have Z : 2 * k = d[X₁ + X₁' # X₂ + X₂'] + d[X₁ | X₁ + X₁' # X₂ | X₂ + X₂'] + I₂ :=
    I_two_aux' h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂'
  have : ρ[X₁ + X₁' # A] ≤ (ρ[X₁ # A] + ρ[X₁ # A] + d[ X₁ # X₁ ]) / 2 := by
    refine (rho_of_sum_le hX₁ hX₁' hA
      (by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide))).trans_eq ?_
    rw [rho_eq_of_identDistrib h₁.symm, h₁.rdist_congr_right hX₁.aemeasurable]
  have : ρ[X₂ + X₂' # A] ≤ (ρ[X₂ # A] + ρ[X₂ # A] + d[ X₂ # X₂ ]) / 2 := by
    refine (rho_of_sum_le hX₂ hX₂' hA
      (by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide))).trans_eq ?_
    rw [rho_eq_of_identDistrib h₂.symm, h₂.rdist_congr_right hX₂.aemeasurable]
  have : ρ[X₁ | X₁ + X₁' # A] ≤ (ρ[X₁ # A] + ρ[X₁ # A] + d[ X₁ # X₁ ]) / 2 := by
    refine (condRho_of_sum_le hX₁ hX₁' hA
      (by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide))).trans_eq ?_
    rw [rho_eq_of_identDistrib h₁.symm, h₁.rdist_congr_right hX₁.aemeasurable]
  have : ρ[X₂ | X₂ + X₂' # A] ≤ (ρ[X₂ # A] + ρ[X₂ # A] + d[ X₂ # X₂ ]) / 2 := by
    refine (condRho_of_sum_le hX₂ hX₂' hA
      (by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide))).trans_eq ?_
    rw [rho_eq_of_identDistrib h₂.symm, h₂.rdist_congr_right hX₂.aemeasurable]
  have : I₂ ≤ η * (d[X₁ # X₁] + d[X₂ # X₂]) := by nlinarith
  rw [rdist_add_rdist_eq h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂'] at this
  have one_eta : 0 < 1 - η := by linarith
  apply (mul_le_mul_iff_of_pos_left one_eta).1
  have : (1 - η) * I₂ ≤ 2 * η * k - I₁ * η := by linarith
  apply this.trans_eq
  field_simp
  ring

/- ****************************************
End Game
******************************************* -/

include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
$$d[X_1;X_2]\le 3\bbI[T_1:T_2\mid T_3] + (2\bbH[T_3]-\bbH[T_1]-\bbH[T_2])
  + \eta(\rho(T_1|T_3)+\rho(T_2|T_3)-\rho(X_1)-\rho(X_2)).$$ -/
lemma dist_le_of_sum_zero {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    [IsProbabilityMeasure μ] {T₁ T₂ T₃ : Ω' → G}
    (hsum : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) :
    k ≤ 3 * I[T₁ : T₂ ; μ] + (2 * H[T₃ ; μ] - H[T₁ ; μ] - H[T₂ ; μ])
      + η * (ρ[T₁ | T₃ ; μ # A] + ρ[T₂ | T₃ ; μ #  A] - ρ[X₁ # A] - ρ[X₂ # A]) := by
  cases nonempty_fintype G
  let _ : MeasureSpace Ω' := ⟨μ⟩
  have : μ = ℙ := rfl
  simp only [this]
  have : ∑ t, (Measure.real ℙ (T₃ ⁻¹' {t})) * d[ X₁ # X₂ ] ≤ ∑ t, (Measure.real ℙ (T₃ ⁻¹' {t})) *
      (d[T₁ ; ℙ[|T₃ ← t] # T₂ ; ℙ[|T₃ ← t]]
        + η * (ρ[T₁ ; ℙ[|T₃ ← t] # A] - ρ[X₁ # A]) + η * (ρ[T₂ ; ℙ[|T₃ ← t] # A] - ρ[X₂ # A])) := by
    apply Finset.sum_le_sum (fun t ht ↦ ?_)
    rcases eq_or_ne (Measure.real ℙ (T₃ ⁻¹' {t})) 0 with h't | h't
    · simp [h't]
    have : IsProbabilityMeasure (ℙ[|T₃ ← t]) := cond_isProbabilityMeasure_of_real h't
    gcongr
    exact le_rdist_of_phiMinimizes' h_min hT₁ hT₂
  have : k ≤ ∑ x : G, (Measure.real ℙ (T₃ ⁻¹' {x})) * d[T₁ ; ℙ[|T₃ ← x] # T₂ ; ℙ[|T₃ ← x]] +
      η * (ρ[T₁ | T₃ # A] - ρ[X₁ # A]) + η * (ρ[T₂ | T₃ # A] - ρ[X₂ # A]) := by
    have S : ∑ i : G, (Measure.real ℙ (T₃ ⁻¹' {i})) = 1 := by
      have : IsProbabilityMeasure (Measure.map T₃ ℙ) := isProbabilityMeasure_map hT₃.aemeasurable
      simp [← map_measureReal_apply hT₃ (measurableSet_singleton _)]
    simp_rw [← Finset.sum_mul, S, mul_add, Finset.sum_add_distrib, ← mul_assoc, mul_comm _ η,
      mul_assoc, ← Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_sub,
      ← Finset.sum_mul, S] at this
    simpa [mul_sub, condRho, tsum_fintype] using this
  have J : ∑ x : G, (Measure.real ℙ (T₃ ⁻¹' {x})) * d[T₁ ; ℙ[|T₃ ← x] # T₂ ; ℙ[|T₃ ← x]]
      ≤ 3 * I[T₁ : T₂] + 2 * H[T₃] - H[T₁] - H[T₂] := by
    have h2T₃ : T₃ = T₁ + T₂ :=
      calc T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hsum, _root_.zero_sub]; simp [ZModModule.neg_eq_self]
        _ = T₁ + T₂ := by rw [add_sub_cancel_right]
    subst h2T₃
    simpa [integral_fintype _ Integrable.of_finite, map_measureReal_apply hT₃ (.singleton _)]
      using ent_bsg hT₁ hT₂ (μ := ℙ)
  linarith

include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
$$d[X_1;X_2]\le 3\bbI[T_1:T_2\mid T_3] + (2\bbH[T_3]-\bbH[T_1]-\bbH[T_2])+ \eta(\rho(T_1|T_3)
  +\rho(T_2|T_3)-\rho(X_1)-\rho(X_2)).$$ -/
lemma dist_le_of_sum_zero_cond {Ω' : Type*} [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω')] {T₁ T₂ T₃ S : Ω' → G}
    (hsum : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)
    (hS : Measurable S) :
    k ≤ 3 * I[T₁ : T₂ | S] + (2 * H[T₃ | S] - H[T₁ | S] - H[T₂ | S])
      + η * (ρ[T₁ | ⟨T₃, S⟩ # A] + ρ[T₂ | ⟨T₃, S⟩ #  A] - ρ[X₁ # A] - ρ[X₂ # A]) := by
  cases nonempty_fintype G
  have hw (a : ℝ) : a = ∑ w, (Measure.real ℙ (S ⁻¹' {w})) * a := by
    have : IsProbabilityMeasure (map S ℙ) := isProbabilityMeasure_map hS.aemeasurable
    simp_rw [← Finset.sum_mul, ← map_measureReal_apply hS (MeasurableSet.singleton _),
      sum_measureReal_singleton]
    simp
  rw [condMutualInfo_eq_sum' hS, condEntropy_eq_sum_fintype _ _ _ hS,
    condEntropy_eq_sum_fintype _ _ _ hS, condEntropy_eq_sum_fintype _ _ _ hS,
    condRho_prod_eq_sum hT₃ hS, condRho_prod_eq_sum hT₃ hS, hw k, hw ρ[X₁ # A], hw ρ[X₂ # A]]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, mul_sub, mul_add]
  gcongr with g hg
  rcases eq_or_ne (Measure.real ℙ (S ⁻¹' {g})) 0 with hpg | hpg
  · simp [hpg]
  set μ := ℙ[|S ← g]
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_real hpg
  have := dist_le_of_sum_zero (μ := μ) h_min hsum hT₁ hT₂ hT₃
  have := mul_le_mul_of_nonneg_left this (show 0 ≤ (Measure.real ℙ (S ⁻¹' {g})) by simp)
  linarith

include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2] \leq \sum_{1 \leq i < j \leq 3} \bbI[T_i:T_j]
  + \frac{\eta}{3} \sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j) + \rho(T_j|T_i) -\rho(X_1)-\rho(X_2))$$
-/
lemma dist_le_of_sum_zero' {Ω' : Type*} [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω')] {T₁ T₂ T₃ : Ω' → G} (hsum : T₁ + T₂ + T₃ = 0)
    (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) :
    k ≤ I[T₁ : T₂] + I[T₁ : T₃] + I[T₂ : T₃]
      + (η / 3) * ((ρ[T₁ | T₂ # A] + ρ[T₂ | T₁ # A] - ρ[X₁ # A] - ρ[X₂ # A])
                 + (ρ[T₁ | T₃ # A] + ρ[T₃ | T₁ # A] - ρ[X₁ # A] - ρ[X₂ # A])
                 + (ρ[T₂ | T₃ # A] + ρ[T₃ | T₂ # A] - ρ[X₁ # A] - ρ[X₂ # A])) := by
  have := dist_le_of_sum_zero h_min hsum hT₁ hT₂ hT₃ (μ := ℙ)
  have : T₁ + T₃ + T₂ = 0 := by convert hsum using 1; abel
  have := dist_le_of_sum_zero h_min this hT₁ hT₃ hT₂ (μ := ℙ)
  have : T₂ + T₃ + T₁ = 0 := by convert hsum using 1; abel
  have := dist_le_of_sum_zero h_min this hT₂ hT₃ hT₁ (μ := ℙ)
  linarith

include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2] \leq \sum_{1 \leq i < j \leq 3} \bbI[T_i:T_j]
  + \frac{\eta}{3} \sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j) + \rho(T_j|T_i) -\rho(X_1)-\rho(X_2))$$
-/
lemma dist_le_of_sum_zero_cond' {Ω' : Type*} [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω')] {T₁ T₂ T₃ : Ω' → G} (S : Ω' → G)
    (hsum : T₁ + T₂ + T₃ = 0)
    (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) (hS : Measurable S) :
    k ≤ I[T₁ : T₂ | S] + I[T₁ : T₃| S] + I[T₂ : T₃ | S]
      + (η / 3) * ((ρ[T₁ | ⟨T₂, S⟩ # A] + ρ[T₂ | ⟨T₁, S⟩ # A] - ρ[X₁ # A] - ρ[X₂ # A])
                 + (ρ[T₁ | ⟨T₃, S⟩ # A] + ρ[T₃ | ⟨T₁, S⟩ # A] - ρ[X₁ # A] - ρ[X₂ # A])
                 + (ρ[T₂ | ⟨T₃, S⟩ # A] + ρ[T₃ | ⟨T₂, S⟩ # A] - ρ[X₁ # A] - ρ[X₂ # A])) := by
  have := dist_le_of_sum_zero_cond h_min hsum hT₁ hT₂ hT₃ hS
  have : T₁ + T₃ + T₂ = 0 := by convert hsum using 1; abel
  have := dist_le_of_sum_zero_cond h_min this hT₁ hT₃ hT₂ hS
  have : T₂ + T₃ + T₁ = 0 := by convert hsum using 1; abel
  have := dist_le_of_sum_zero_cond h_min this hT₂ hT₃ hT₁ hS
  linarith

lemma new_gen_ineq_aux1 {Y₁ Y₂ Y₃ Y₄ : Ω → G}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
    (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
    ρ[Y₁ + Y₂ | ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ # A] ≤
      (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 4
        + (d[Y₁ # Y₂] + d[Y₃ # Y₄]) / 4 + (d[Y₁ + Y₂ # Y₃ + Y₄]
          + I[Y₁ + Y₂ : Y₁ + Y₃ | Y₁ + Y₂ + Y₃ + Y₄]) / 2 := by
  set S := Y₁ + Y₂ + Y₃ + Y₄
  set T₁ := Y₁ + Y₂
  set T₂ := Y₁ + Y₃
  set T₁' := Y₃ + Y₄
  set T₂' := Y₂ + Y₄
  have : ρ[T₁ | ⟨T₂, S⟩ # A] ≤ ρ[T₁ | S # A] + I[T₁ : T₂ | S] / 2 := by
    rw [condMutualInfo_eq' (by fun_prop) (by fun_prop) (by fun_prop)]
    exact condRho_prod_le (by fun_prop) (by fun_prop) (by fun_prop) hA
  have : ρ[T₁ | S # A] ≤ (ρ[T₁ # A] + ρ[T₁' # A] + d[T₁ # T₁']) / 2 := by
    have S_eq : S = T₁ + T₁' := by simp only [S, T₁, T₁']; abel
    rw [S_eq]
    apply condRho_of_sum_le (by fun_prop) (by fun_prop) hA
    exact h_indep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption) 0 1 2 3
      (by decide) (by decide) (by decide) (by decide)
  have : ρ[T₁ # A] ≤ (ρ[Y₁ # A] + ρ[Y₂ # A] + d[Y₁ # Y₂]) / 2 :=
    rho_of_sum_le hY₁ hY₂ hA (h_indep.indepFun (i := 0) (j := 1) (by decide))
  have : ρ[T₁' # A] ≤ (ρ[Y₃ # A] + ρ[Y₄ # A] + d[Y₃ # Y₄]) / 2 :=
    rho_of_sum_le hY₃ hY₄ hA (h_indep.indepFun (i := 2) (j := 3) (by decide))
  linarith

lemma new_gen_ineq_aux2 {Y₁ Y₂ Y₃ Y₄ : Ω → G}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
    (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
    ρ[Y₁ + Y₂ | ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ # A] ≤
       (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 4
        + (d[Y₁ # Y₃] + d[Y₂ # Y₄]) / 4 + d[Y₁ | Y₁ + Y₃ # Y₂ | Y₂ + Y₄] / 2 := by
  cases nonempty_fintype G
  set S := Y₁ + Y₂ + Y₃ + Y₄
  set T₁ := Y₁ + Y₂
  set T₂ := Y₁ + Y₃
  set T₁' := Y₃ + Y₄
  set T₂' := Y₂ + Y₄
  have I : IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩) := by
    refine (h_indep.indepFun_prodMk_prodMk ?_ 0 2 1 3
      (by decide) (by decide) (by decide) (by decide))
    intro i; fin_cases i <;> assumption
  calc
  ρ[Y₁ + Y₂ | ⟨T₂, S⟩ # A]
    = ρ[Y₁ + Y₂ | ⟨T₂, T₂'⟩ # A] := by
      have : S = T₂ + T₂' := by simp only [S, T₂, T₂']; abel
      rw [this]
      let e : G × G ≃ G × G :=
        { toFun p := ⟨p.1, p.1 + p.2⟩
          invFun p := ⟨p.1, p.2 - p.1⟩
          left_inv := by intro ⟨a, b⟩; simp
          right_inv := by intro ⟨a, b⟩; simp }
      exact condRho_of_injective T₁ (⟨T₂, T₂'⟩) (f := e) (A := A) e.injective
  _ = ∑ w, (Measure.real ℙ (⟨T₂, T₂'⟩ ⁻¹' {w})) * ρ[Y₁ + Y₂ ; ℙ[|⟨T₂, T₂'⟩ ← w] # A] := by
    rw [condRho, tsum_fintype]
  _ ≤ ∑ w, (Measure.real ℙ (⟨T₂, T₂'⟩ ⁻¹' {w})) * ((ρ[Y₁ ; ℙ[|⟨T₂, T₂'⟩ ← w] # A] +
      ρ[Y₂ ; ℙ[|⟨T₂, T₂'⟩ ← w] # A] + d[Y₁ ; ℙ[|⟨T₂, T₂'⟩ ← w] # Y₂ ; ℙ[|⟨T₂, T₂'⟩ ← w]]) / 2) := by
    gcongr with w hw
    have : IndepFun Y₁ Y₂ (ℙ[|⟨T₂, T₂'⟩ ⁻¹' {w}]) := by
      have E : (⟨Y₁, Y₃⟩)⁻¹' {p | p.1 + p.2 = w.1} ∩ (⟨Y₂, Y₄⟩)⁻¹' {p | p.1 + p.2 = w.2}
        = ⟨T₂, T₂'⟩ ⁻¹' {w} := by aesop
      have I : IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩) (ℙ[|(⟨Y₁, Y₃⟩)⁻¹' {p | p.1 + p.2 = w.1}
          ∩ (⟨Y₂, Y₄⟩)⁻¹' {p | p.1 + p.2 = w.2}]) :=
        I.cond (measurable_add (.singleton w.1))
          (measurable_add (.singleton w.2)) (hY₁.prodMk hY₃) (hY₂.prodMk hY₄)
      rw [E] at I
      exact I.comp measurable_fst measurable_fst
    exact rho_of_sum_le hY₁ hY₂ hA this
  _ = (ρ[Y₁ | ⟨T₂, T₂'⟩ # A] + ρ[Y₂ | ⟨T₂, T₂'⟩ # A] + d[Y₁ | T₂ # Y₂ | T₂']) / 2 := by
    simp_rw [← mul_div_assoc, ← Finset.sum_div, mul_add, Finset.sum_add_distrib, condRho,
      tsum_fintype]
    congr
    rw [condRuzsaDist_eq_sum' hY₁ (by fun_prop) hY₂ (by fun_prop), Fintype.sum_prod_type]
    congr with x
    congr with y
    have : (⟨T₂, T₂'⟩) ⁻¹' {(x, y)} = (Y₁ + Y₃) ⁻¹' {x} ∩ (Y₂ + Y₄) ⁻¹' {y} := by
      ext p; simp [T₂, T₂']
    rw [this]
    have J : IndepFun (Y₁ + Y₃) (Y₂ + Y₄) := by exact I.comp measurable_add measurable_add
    rw [J.measureReal_inter_preimage_eq_mul (.singleton x) (.singleton y)]
    rcases eq_or_ne (Measure.real ℙ ((Y₁ + Y₃) ⁻¹' {x})) 0 with h1|h1
    · simp [h1, T₂]
    rcases eq_or_ne (Measure.real ℙ ((Y₂ + Y₄) ⁻¹' {y})) 0 with h2|h2
    · simp [h2, T₂']
    congr 1
    have A : IdentDistrib Y₁ Y₁ (ℙ[|(Y₁ + Y₃) ⁻¹' {x} ∩ (Y₂ + Y₄) ⁻¹' {y}])
        (ℙ[|(Y₁ + Y₃) ⁻¹' {x}]) := by
      rw [← cond_cond_eq_cond_inter' (by exact hY₁.add hY₃ (.singleton _))
        (by exact hY₂.add hY₄ (.singleton _)) (by finiteness)]
      have : IsProbabilityMeasure (ℙ[|(Y₁ + Y₃) ⁻¹' {x}]) := cond_isProbabilityMeasure_of_real h1
      apply (IndepFun.identDistrib_cond _ (.singleton _) hY₁ (by fun_prop) _).symm
      · have : IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩) (ℙ[|(⟨Y₁, Y₃⟩) ⁻¹' {p | p.1 + p.2 = x}]) :=
          I.cond_left (measurable_add (.singleton x)) (hY₁.prodMk hY₃)
        exact this.comp measurable_fst measurable_add
      · rw [cond_apply, J.measure_inter_preimage_eq_mul _ _ (.singleton x) (.singleton y)]
        · simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h1 h2
          simp [h1, h2]
        · exact hY₁.add hY₃ (.singleton _)
    refine A.rdist_congr ?_
    rw [Set.inter_comm, ← cond_cond_eq_cond_inter' (by exact hY₂.add hY₄ (.singleton _))
      (by exact hY₁.add hY₃ (.singleton _)) (by finiteness)]
    have : IsProbabilityMeasure (ℙ[|(Y₂ + Y₄) ⁻¹' {y}]) := cond_isProbabilityMeasure_of_real h2
    apply (IndepFun.identDistrib_cond _ (.singleton _) hY₂ (hY₁.add hY₃) _).symm
    · have : IndepFun (⟨Y₂, Y₄⟩) (⟨Y₁, Y₃⟩) (ℙ[|(⟨Y₂, Y₄⟩) ⁻¹' {p | p.1 + p.2 = y}]) :=
        I.symm.cond_left (measurable_add (.singleton y)) (hY₂.prodMk hY₄)
      exact this.comp measurable_fst measurable_add
    · rw [Pi.add_def, cond_apply (hY₂.add hY₄ (.singleton y)), ← Pi.add_def, ← Pi.add_def,
        J.symm.measure_inter_preimage_eq_mul _ _ (.singleton _) (.singleton _)]
      simp only [ne_eq, measure_ne_top, not_false_eq_true, measureReal_eq_zero_iff] at h1 h2
      simp [h1, h2]
  _ = (ρ[Y₁ | T₂ # A] + ρ[Y₂ | T₂' # A] + d[Y₁ | T₂ # Y₂ | T₂']) / 2 := by
    congr 3
    · apply condRho_prod_eq_of_indepFun hY₁ (by fun_prop) (by fun_prop)
      exact I.comp (measurable_fst.prodMk measurable_add) measurable_add
    · have : ρ[Y₂ | ⟨T₂, T₂'⟩ # A] = ρ[Y₂ | ⟨T₂', T₂⟩ # A] :=
        condRho_of_injective Y₂ (⟨T₂', T₂⟩) (f := Prod.swap) Prod.swap_injective
      rw [this]
      apply condRho_prod_eq_of_indepFun hY₂ (by fun_prop) (by fun_prop)
      exact I.symm.comp (measurable_fst.prodMk measurable_add) measurable_add
  _ ≤ ((ρ[Y₁ # A] + ρ[Y₃ # A] + d[Y₁ # Y₃]) / 2 +
       (ρ[Y₂ # A] + ρ[Y₄ # A] + d[Y₂ # Y₄]) / 2 + d[Y₁ | T₂ # Y₂ | T₂']) / 2 := by
    gcongr
    · exact condRho_of_sum_le hY₁ hY₃ hA (h_indep.indepFun (i := 0) (j := 2) (by decide))
    · exact condRho_of_sum_le hY₂ hY₄ hA (h_indep.indepFun (i := 1) (j := 3) (by decide))
  _ = (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 4
        + (d[Y₁ # Y₃] + d[Y₂ # Y₄]) / 4 + d[Y₁ | Y₁ + Y₃ # Y₂ | Y₂ + Y₄] / 2 := by ring

lemma new_gen_ineq {Y₁ Y₂ Y₃ Y₄ : Ω → G}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
    (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
    ρ[Y₁ + Y₂ | ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ # A] ≤
      (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 4
        + (d[Y₁ # Y₂] + d[Y₃ # Y₄] + d[Y₁ # Y₃] + d[Y₂ # Y₄]) / 8 + (d[Y₁ + Y₂ # Y₃ + Y₄]
          + I[Y₁ + Y₂ : Y₁ + Y₃ | Y₁ + Y₂ + Y₃ + Y₄] + d[Y₁ | Y₁ + Y₃ # Y₂ | Y₂ + Y₄]) / 4 := by
  have := new_gen_ineq_aux1 hY₁ hY₂ hY₃ hY₄ h_indep hA
  have := new_gen_ineq_aux2 hY₁ hY₂ hY₃ hY₄ h_indep hA
  linarith

/-- For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define
$S:=Y_1+Y_2+Y_3+Y_4$, $T_1:=Y_1+Y_2$, $T_2:=Y_1+Y_3$. Then
  $$\rho(T_1|T_2,S)+\rho(T_2|T_1,S) - \frac{1}{2}\sum_{i} \rho(Y_i)
    \le \frac{1}{2}(d[Y_1;Y_2]+d[Y_3;Y_4]+d[Y_1;Y_3]+d[Y_2;Y_4]).$$
-/
lemma condRho_sum_le {Y₁ Y₂ Y₃ Y₄ : Ω → G}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
    (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
    ρ[Y₁ + Y₂ | ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ # A] + ρ[Y₁ + Y₃ | ⟨Y₁ + Y₂, Y₁ + Y₂ + Y₃ + Y₄⟩ # A] -
      (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 2 ≤
        (d[Y₁ # Y₂] + d[Y₃ # Y₄] + d[Y₁ # Y₃] + d[Y₂ # Y₄]) / 2 := by
  set S := Y₁ + Y₂ + Y₃ + Y₄
  set T₁ := Y₁ + Y₂
  set T₂ := Y₁ + Y₃
  set T₁' := Y₃ + Y₄
  set T₂' := Y₂ + Y₄
  have J : ρ[T₁ | ⟨T₂, S⟩ # A] ≤
    (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 4
      + (d[Y₁ # Y₂] + d[Y₃ # Y₄] + d[Y₁ # Y₃] + d[Y₂ # Y₄]) / 8 + (d[Y₁ + Y₂ # Y₃ + Y₄]
        + I[Y₁ + Y₂ : Y₁ + Y₃ | Y₁ + Y₂ + Y₃ + Y₄] + d[Y₁ | Y₁ + Y₃ # Y₂ | Y₂ + Y₄]) / 4 :=
    new_gen_ineq hY₁ hY₂ hY₃ hY₄ h_indep hA
  have J' : ρ[T₂ | ⟨T₁, Y₁ + Y₃ + Y₂ + Y₄⟩ # A] ≤
    (ρ[Y₁ # A] + ρ[Y₃ # A] + ρ[Y₂ # A] + ρ[Y₄ # A]) / 4
      + (d[Y₁ # Y₃] + d[Y₂ # Y₄] + d[Y₁ # Y₂] + d[Y₃ # Y₄]) / 8 + (d[Y₁ + Y₃ # Y₂ + Y₄]
        + I[Y₁ + Y₃ : Y₁ + Y₂|Y₁ + Y₃ + Y₂ + Y₄] + d[Y₁ | Y₁ + Y₂ # Y₃ | Y₃ + Y₄]) / 4 :=
    new_gen_ineq hY₁ hY₃ hY₂ hY₄ h_indep.reindex_four_acbd hA
  have : Y₁ + Y₃ + Y₂ + Y₄ = S := by simp only [S]; abel
  rw [this] at J'
  have : d[Y₁ + Y₂ # Y₃ + Y₄] + I[Y₁ + Y₂ : Y₁ + Y₃ | Y₁ + Y₂ + Y₃ + Y₄]
    + d[Y₁ | Y₁ + Y₃ # Y₂ | Y₂ + Y₄] + d[Y₁ + Y₃ # Y₂ + Y₄]
    + I[Y₁ + Y₃ : Y₁ + Y₂|S] + d[Y₁ | Y₁ + Y₂ # Y₃ | Y₃ + Y₄]
      = (d[Y₁ # Y₂] + d[Y₃ # Y₄]) + (d[Y₁ # Y₃] + d[Y₂ # Y₄]) := by
    have K : Y₁ + Y₃ + Y₂ + Y₄ = S := by simp only [S]; abel
    have K' : I[Y₁ + Y₃ : Y₁ + Y₂|Y₁ + Y₂ + Y₃ + Y₄] = I[Y₁ + Y₃ : Y₃ + Y₄|Y₁ + Y₂ + Y₃ + Y₄] := by
      have : Measurable (Y₁ + Y₃) := by fun_prop
      rw [condMutualInfo_comm this (by fun_prop), condMutualInfo_comm this (by fun_prop)]
      have B := condMutualInfo_of_inj_map (X := Y₃ + Y₄) (Y := Y₁ + Y₃) (Z := Y₁ + Y₂ + Y₃ + Y₄)
        (by fun_prop) (by fun_prop) (by fun_prop) (fun a b ↦ a - b) (fun a ↦ sub_right_injective)
        (μ := ℙ)
      convert B with g
      simp
    have K'' : I[Y₁ + Y₂ : Y₁ + Y₃|Y₁ + Y₂ + Y₃ + Y₄] = I[Y₁ + Y₂ : Y₂ + Y₄|Y₁ + Y₂ + Y₃ + Y₄] := by
      have : Measurable (Y₁ + Y₂) := by fun_prop
      rw [condMutualInfo_comm this (by fun_prop), condMutualInfo_comm this (by fun_prop)]
      have B := condMutualInfo_of_inj_map (X := Y₂ + Y₄) (Y := Y₁ + Y₂) (Z := Y₁ + Y₂ + Y₃ + Y₄)
        (by fun_prop) (by fun_prop) (by fun_prop) (fun a b ↦ a - b) (fun a ↦ sub_right_injective)
        (μ := ℙ)
      convert B with g
      simp
      abel
    rw [sum_of_rdist_eq_char_2' Y₁ Y₂ Y₃ Y₄ h_indep hY₁ hY₂ hY₃ hY₄,
      sum_of_rdist_eq_char_2' Y₁ Y₃ Y₂ Y₄ h_indep.reindex_four_acbd hY₁ hY₃ hY₂ hY₄, K, K', K'']
    abel
  linarith

/-- For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define
$T_1:=Y_1+Y_2, T_2:=Y_1+Y_3, T_3:=Y_2+Y_3$ and $S:=Y_1+Y_2+Y_3+Y_4$. Then
  $$\sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j,S) + \rho(T_j|T_i,S)
    - \frac{1}{2}\sum_{i} \rho(Y_i))\le \sum_{1\leq i < j \leq 4}d[Y_i;Y_j]$$ -/
lemma condRho_sum_le' {Y₁ Y₂ Y₃ Y₄ : Ω → G}
      (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
      (h_indep : iIndepFun ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
    let S := Y₁ + Y₂ + Y₃ + Y₄
    let T₁ := Y₁ + Y₂
    let T₂ := Y₁ + Y₃
    let T₃ := Y₂ + Y₃
    ρ[T₁ | ⟨T₂, S⟩ # A] + ρ[T₂ | ⟨T₁, S⟩ # A] + ρ[T₁ | ⟨T₃, S⟩ # A] + ρ[T₃ | ⟨T₁, S⟩ # A]
      + ρ[T₂ | ⟨T₃, S⟩ # A] + ρ[T₃ | ⟨T₂, S⟩ # A]
      - 3 * (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 2 ≤
    d[Y₁ # Y₂] + d[Y₁ # Y₃] + d[Y₁ # Y₄] + d[Y₂ # Y₃] + d[Y₂ # Y₄] + d[Y₃ # Y₄] := by
  have K₁ := condRho_sum_le hY₁ hY₂ hY₃ hY₄ h_indep hA
  have K₂ := condRho_sum_le hY₂ hY₁ hY₃ hY₄ h_indep.reindex_four_bacd hA
  have Y₂₁ : Y₂ + Y₁ = Y₁ + Y₂ := by abel
  have dY₂₁ : d[Y₂ # Y₁] = d[Y₁ # Y₂] := rdist_symm
  rw [Y₂₁, dY₂₁] at K₂
  have K₃ := condRho_sum_le hY₃ hY₁ hY₂ hY₄ h_indep.reindex_four_cabd hA
  have Y₃₁ : Y₃ + Y₁ = Y₁ + Y₃ := by abel
  have Y₃₂ : Y₃ + Y₂ = Y₂ + Y₃ := by abel
  have S₃ : Y₁ + Y₃ + Y₂ + Y₄ = Y₁ + Y₂ + Y₃ + Y₄ := by abel
  have dY₃₁ : d[Y₃ # Y₁] = d[Y₁ # Y₃] := rdist_symm
  have dY₃₂ : d[Y₃ # Y₂] = d[Y₂ # Y₃] := rdist_symm
  rw [Y₃₁, Y₃₂, S₃, dY₃₁, dY₃₂] at K₃
  linarith

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min hη in
/-- If $X_1, X_2$ is a $\phi$-minimizer, then $d[X_1;X_2] = 0$. -/
lemma dist_of_min_eq_zero' (hA : A.Nonempty) (hη' : η < 1 / 8) : d[X₁ # X₂] = 0 := by
  let T₁ := X₁ + X₂
  let T₂ := X₁ + X₁'
  let T₃ := X₁' + X₂
  have hsum : T₁ + T₂ + T₃ = 0 := by
    have : T₁ + T₂ + T₃ = 2 • (X₁ + X₁' + X₂) := by simp only [T₁, T₂, T₃]; abel
    rwa [ZModModule.char_nsmul_eq_zero 2 (X₁ + X₁' + X₂)] at this
  let S := X₁ + X₂ + X₁' + X₂'
  have J₁ : k ≤ I₁ + 2 * I₂ + η / 3 *
      (ρ[T₁ | ⟨T₂, S⟩ # A] + ρ[T₂ | ⟨T₁, S⟩ # A] + ρ[T₁ | ⟨T₃, S⟩ # A] + ρ[T₃ | ⟨T₁, S⟩ # A]
        + ρ[T₂ | ⟨T₃, S⟩ # A] + ρ[T₃ | ⟨T₂, S⟩ # A] - 3 * (ρ[X₁ # A] + ρ[X₂ # A])) := by
    have K := dist_le_of_sum_zero_cond' h_min S hsum
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    have : I[T₂ : T₃ | S] = I₂ := by
      rw [condMutualInfo_comm (by fun_prop) (by fun_prop)]
      have : X₁ + X₁' = X₁' + X₁ := by abel
      convert I₃_eq _ _ _ _ hX₁ hX₂ hX₁' hX₂' h₁ h_indep using 2
    linarith
  have J₂ : k ≤ I₁ + 2 * I₂ +
      η / 3 * (k + d[X₁ # X₁'] + d[X₁ # X₂'] + d[X₂ # X₁'] + d[X₂ # X₂'] + d[X₁' # X₂']) := by
    apply J₁.trans
    gcongr
    have W : X₂ + X₁' = X₁' + X₂ := by abel
    have := condRho_sum_le' hX₁ hX₂ hX₁' hX₂' h_indep hA
    simp only [W] at this
    have : ρ[X₁' # A] = ρ[X₁ # A] := rho_eq_of_identDistrib h₁.symm
    have : ρ[X₂' # A] = ρ[X₂ # A] := rho_eq_of_identDistrib h₂.symm
    linarith
  have J₃ : k ≤ I₁ + 2 * I₂ + η / 3 * (6 * k + I₂ - I₁) := by
    apply J₂.trans_eq
    congr 2
    have : d[X₁ # X₁'] = d[X₁ # X₁] := h₁.symm.rdist_congr_right hX₁.aemeasurable
    have : d[X₁ # X₂'] = d[X₁ # X₂] := h₂.symm.rdist_congr_right hX₁.aemeasurable
    have : d[X₂ # X₁'] = d[X₁ # X₂] := by
      rw [rdist_symm]; exact h₁.symm.rdist_congr_left hX₂.aemeasurable
    have : d[X₂ # X₂'] = d[X₂ # X₂] := h₂.symm.rdist_congr_right hX₂.aemeasurable
    have : d[X₁' # X₂'] = d[X₁ # X₂] := h₁.symm.rdist_congr h₂.symm
    have := rdist_add_rdist_eq h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂'
    linarith
  let D := 2 * η * k - I₁
  have J₄ : k ≤ 8 * η * k - (3 - 10 * η) / (3 * (1 - η)) * D := by
    have I₁_eq : I₁ = 2 * η * k - D := by simp only [D]; abel
    have : I₂ ≤ 2 * η * k + η / (1 - η) * D :=
      I_two_le hη h_min h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂' hA (by linarith)
    calc
    k ≤ I₁ + 2 * I₂ + η / 3 * (6 * k + I₂ - I₁) := J₃
    _ = 2 * η * k + I₁ + 2 * I₂ + η / 3 * (I₂ - I₁) := by ring
    _ ≤ 2 * η * k + (2 * η * k - D) + 2 * (2 * η * k + η / (1 - η) * D)
        + η / 3 * ((2 * η * k + η / (1 - η) * D) - (2 * η * k - D)) := by
      rw [I₁_eq]
      gcongr
    _ = 8 * η * k - (3 - 10 * η) / (3 * (1 - η)) * D := by
      have : 1 - η ≠ 0 := ne_of_gt (by linarith)
      field_simp
      ring
  have J₅ : k ≤ 8 * η * k - 0 := by
    apply J₄.trans
    gcongr
    have : 0 ≤ D := sub_nonneg_of_le (I_one_le hη h_min h₁ h₂ h_indep hX₁ hX₂ hX₁' hX₂' hA)
    apply mul_nonneg _ this
    exact div_nonneg (by linarith) (by linarith)
  have : k ≤ 0 := by nlinarith
  exact le_antisymm this (rdist_nonneg hX₁ hX₂)

include hX₁ hX₂ h_min hη in
theorem dist_of_min_eq_zero (hA : A.Nonempty) (hη' : η < 1 / 8) : d[X₁ # X₂] = 0 := by
  let ⟨Ω', m', μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1', h_id2'⟩
    := independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_congr h_id2]
  let _ : MeasureSpace Ω' := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure Ω') := hμ
  have h'_min : phiMinimizes Y₁ Y₂ η A ℙ := phiMinimizes_of_identDistrib h_min h_id1.symm h_id2.symm
  exact dist_of_min_eq_zero' hη h'_min (h_id1.trans h_id1'.symm) (h_id2.trans h_id2'.symm)
     h_indep hY₁ hY₂ hY₁' hY₂'  hA hη'

open Filter
open scoped Topology

/-- For `η ≤ 1/8`, there exist phi-minimizers `X₁, X₂` at zero Rusza distance. For `η < 1/8`,
all minimizers are fine, by `dist_of_min_eq_zero`. For `η = 1/8`, we use a limit of
minimizers for `η < 1/8`, which exists by compactness. -/
lemma phiMinimizer_exists_rdist_eq_zero (hA : A.Nonempty) :
    ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
      Measurable X₁ ∧ Measurable X₂ ∧ IsProbabilityMeasure (ℙ : Measure Ω)
      ∧ phiMinimizes X₁ X₂ (1/8 : ℝ) A ℙ ∧ d[X₁ # X₂] = 0 := by
    -- let `uₙ` be a sequence converging from below to `η`. In particular, `uₙ < 1/8`.
  obtain ⟨u, -, u_mem, u_lim⟩ :
      ∃ u, StrictMono u ∧ (∀ (n : ℕ), u n ∈ Set.Ioo 0 (1/8 : ℝ)) ∧ Tendsto u atTop (𝓝 (1/8)) :=
    exists_seq_strictMono_tendsto' (by norm_num)
  -- For each `n`, consider a minimizer associated to `η = uₙ`.
  have : ∀ n, ∃ (μ : Measure (G × G)), IsProbabilityMeasure μ ∧
      phiMinimizes Prod.fst Prod.snd (u n) A μ := fun n ↦ phi_min_exists hA
  choose μ μ_prob hμ using this
  -- extract a converging subsequence of the sequence of minimizers, seen as pairs of probability
  -- measures on `G` (which is a compact space).
  let μ' : ℕ → ProbabilityMeasure (G × G) := fun n ↦ ⟨μ n, μ_prob n⟩
  let _i : TopologicalSpace G := (⊥ : TopologicalSpace G)
  have : DiscreteTopology G := ⟨rfl⟩
  -- The limiting pair of measures will be the desired minimizer.
  rcases IsCompact.tendsto_subseq (x := μ') isCompact_univ (fun n ↦ mem_univ _)
    with ⟨ν, -, φ, φmono, hν⟩
  have φlim : Tendsto φ atTop atTop := φmono.tendsto_atTop
  let M : MeasureSpace (G × G) := ⟨ν⟩
  have : IsProbabilityMeasure (ℙ : Measure (G × G)) := ν.instIsProbabilityMeasureToMeasure
  refine ⟨G × G, M, Prod.fst, Prod.snd, measurable_fst, measurable_snd, by infer_instance, ?_, ?_⟩
  -- check that it is indeed a minimizer, as a limit of minimizers.
  · intro Ω' mΩ' X' Y' hP hX' hY'
    have I n : phi Prod.fst Prod.snd (u n) A (μ n) ≤ phi X' Y' (u n) A ℙ :=
      hμ n _ _ _ _ hP hX' hY'
    have L1 : Tendsto (fun n ↦ phi Prod.fst Prod.snd (u (φ n)) A (μ (φ n))) atTop
        (𝓝 (phi Prod.fst Prod.snd (1/8) A ν)) := by
      apply Tendsto.add
      · apply tendsto_rdist_probabilityMeasure continuous_fst continuous_snd hν
      apply Tendsto.mul (u_lim.comp φlim)
      apply Tendsto.add
      · apply tendsto_rho_probabilityMeasure continuous_fst hA hν
      · apply tendsto_rho_probabilityMeasure continuous_snd hA hν
    have L2 : Tendsto (fun n ↦ phi X' Y' (u (φ n)) A ℙ) atTop (𝓝 (phi X' Y' (1/8) A ℙ)) :=
      Tendsto.const_add _ (Tendsto.mul_const _ (u_lim.comp φlim))
    exact le_of_tendsto_of_tendsto' L1 L2 (fun n ↦ I _)
  -- check that it has zero Rusza distance, as a limit of a sequence at zero Rusza distance.
  · -- The minimizer associated to `uₙ` is at zero Rusza distance of itself, by
    -- lemma `tau_strictly_decreases'`.
    have I0 n : d[Prod.fst ; μ n # Prod.snd ; μ n] = 0 := by
      let M : MeasureSpace (G × G) := ⟨μ n⟩
      apply dist_of_min_eq_zero (u_mem n).1 (hμ n) measurable_fst measurable_snd hA (u_mem n).2
    have : Tendsto (fun x ↦ d[Prod.fst ; μ (φ x) # Prod.snd ; μ (φ x)]) atTop
        (𝓝 d[@Prod.fst G G # @Prod.snd G G]) := by
      apply tendsto_rdist_probabilityMeasure continuous_fst continuous_snd hν
    simp_rw [I0, tendsto_const_nhds_iff] at this
    exact this.symm

end phiMinimizer

section PFR

variable {G : Type uG} [AddCommGroup G] [Finite G] [Module (ZMod 2) G]
{Ω : Type uG} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {A : Finset G}

/-- For any random variables $Y_1,Y_2$, there exist a subgroup $H$ such that
  $$ 2\rho(U_H) \leq \rho(Y_1) + \rho(Y_2) + 8 d[Y_1;Y_2].$$ -/
theorem rho_PFR_conjecture [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (Y₁ Y₂ : Ω → G) (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (A : Finset G) (hA : A.Nonempty) :
    ∃ (H : Submodule (ZMod 2) G) (Ω' : Type uG) (mΩ' : MeasureSpace Ω') (U : Ω' → G),
    IsProbabilityMeasure (ℙ : Measure Ω') ∧ Measurable U ∧
    IsUniform H U ∧ 2 * ρ[U # A] ≤ ρ[Y₁ # A] + ρ[Y₂ # A] + 8 * d[Y₁ # Y₂] := by
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, hP, htau_min, hdist⟩ := phiMinimizer_exists_rdist_eq_zero hA
  wlog h : ρ[X₁ # A] ≤ ρ[X₂ # A] generalizing X₁ X₂
  · rw [rdist_symm] at hdist
    exact this X₂ X₁ hX₂ hX₁ (phiMinimizes_comm htau_min) hdist (by linarith)
  -- use for `U` a translate of `X` to make sure that `0` is in its support.
  obtain ⟨x₀, h₀⟩ : ∃ x₀, ℙ (X₁⁻¹' {x₀}) ≠ 0 := by
    by_contra! h
    have A a : (ℙ : Measure Ω').map X₁ {a} = 0 := by
      rw [Measure.map_apply hX₁ .of_discrete]
      exact h _
    have B : (ℙ : Measure Ω').map X₁ = 0 := by
      rw [← Measure.sum_smul_dirac (μ := (ℙ : Measure Ω').map X₁)]
      simp [A]
    have : IsProbabilityMeasure ((ℙ : Measure Ω').map X₁) :=
      isProbabilityMeasure_map hX₁.aemeasurable
    exact IsProbabilityMeasure.ne_zero _ B
  have h_unif : IsUniform (symmGroup X₁ hX₁) (fun ω ↦ X₁ ω - x₀) := by
    have h' : d[X₁ # X₁] = 0 := by
      apply le_antisymm _ (rdist_nonneg hX₁ hX₁)
      calc
        d[X₁ # X₁] ≤ d[X₁ # X₂] + d[X₂ # X₁] := rdist_triangle hX₁ hX₂ hX₁
        _ = 0 := by rw [hdist, rdist_symm, hdist, zero_add]
    exact isUniform_sub_const_of_rdist_eq_zero hX₁ h' h₀
  refine ⟨AddSubgroup.toZModSubmodule 2 (symmGroup X₁ hX₁), Ω', by infer_instance,
    fun ω ↦ X₁ ω - x₀, by infer_instance, by fun_prop, by exact h_unif, ?_⟩
  have J : d[X₁ # X₂] + (1/8) * (ρ[X₁ # A] + ρ[X₂ # A])
      ≤ d[Y₁ # Y₂] + (1/8) * (ρ[Y₁ # A] + ρ[Y₂ # A]) := by
    have Z := le_rdist_of_phiMinimizes htau_min hY₁ hY₂ (μ₁ := ℙ) (μ₂ := ℙ)
    linarith
  rw [hdist, zero_add] at J
  have : ρ[fun ω ↦ X₁ ω - x₀ # A] = ρ[X₁ # A] := by
    simp_rw [sub_eq_add_neg, rho_of_translate hX₁ hA]
  linarith

/-- If $|A+A| \leq K|A|$, then there exists a subgroup $H$ and $t\in G$ such that
$|A \cap (H+t)| \geq K^{-4} \sqrt{|A||V|}$, and $|H|/|A|\in[K^{-8},K^8]$. -/
lemma better_PFR_conjecture_aux0 {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (t : G),
      K ^ (-4 : ℤ) * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (1 / 2 : ℝ)
        ≤ Nat.card ↑(A ∩ (H + {t})) ∧
      Nat.card A ≤ K ^ 8 * (H : Set G).ncard ∧ (H : Set G).ncard ≤ K ^ 8 * Nat.card A := by
  have A_fin : Finite A := by infer_instance
  classical
  let mG : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := ⟨fun _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' (Set.toFinite _) h₀A hA
  let A' := A.toFinite.toFinset
  have h₀A' : Finset.Nonempty A' := by simpa [A', Finset.Nonempty]
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' h₀A' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -⟩
  rw [hAA'] at UAunif
  have hadd_sub : A + A = A - A := by ext; simp [Set.mem_add, Set.mem_sub, ZModModule.sub_eq_add]
  rw [hadd_sub] at hA
  have : d[UA # UA] ≤ log K := rdist_le_of_isUniform_of_card_add_le h₀A hA UAunif UAmeas
  rw [← hadd_sub] at hA
  -- entropic PFR gives a subgroup `H` which is close to `A` for the rho functional
  rcases rho_PFR_conjecture UA UA UAmeas UAmeas A' h₀A'
    with ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  have ineq : ρ[UH # A'] ≤ 4 * log K := by
    rw [← hAA'] at UAunif
    have : ρ[UA # A'] = 0 := rho_of_uniform UAunif UAmeas h₀A'
    linarith
  set r := 4 * log K with hr
  have J : K ^ (-4 : ℤ) = exp (-r) := by
    rw [hr, ← neg_mul, mul_comm, exp_mul, exp_log K_pos]
    norm_cast
  have J' : K ^ 8 = exp (2 * r) := by
    have : 2 * r = 8 * log K := by ring
    rw [this, mul_comm, exp_mul, exp_log K_pos]
    norm_cast
  rw [J, J']
  refine ⟨H, ?_⟩
  have Z := rho_of_submodule UHunif h₀A' UHmeas r ineq
  have : Nat.card A = Nat.card A' := by simp [← hAA']
  have I t : t +ᵥ (H : Set G) = (H : Set G) + {t} := by
    ext z; simp [mem_vadd_set_iff_neg_vadd_mem, add_comm]
  simp_rw [← I]
  convert Z
  exact hAA'.symm

/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup $H$
such that $A$ can be covered by at most $K^5 |A|^{1/2} / |H|^{1/2}$ cosets of $H$, and $H$ has
the same cardinality as $A$ up to a multiplicative factor $K^8$. -/
lemma better_PFR_conjecture_aux {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c ≤ K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * ((H : Set G).ncard : ℝ) ^ (-1 / 2 : ℝ)
      ∧ (H : Set G).ncard ≤ K ^ 8 * Nat.card A
      ∧ Nat.card A ≤ K ^ 8 * (H : Set G).ncard ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' (Set.toFinite _) h₀A hA
  rcases better_PFR_conjecture_aux0 h₀A hA with ⟨H, x₀, J, IAH, IHA⟩
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos
    positivity
  have Hne : Set.Nonempty (A ∩ (H + {x₀})) := by
    by_contra h'
    have : 0 < (H : Set G).ncard := Nat.card_pos
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    simp only [Nat.card_eq_fintype_card, CharP.cast_eq_zero, lt_self_iff_false,
      not_nonempty_iff_eq_empty.1 h', Fintype.card_ofIsEmpty] at this
    /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  have Z3 :
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ) ≤ (K ^ 5 * Nat.card A ^ (1/2 : ℝ) *
        (H : Set G).ncard ^ (-1/2 : ℝ)) * Nat.card ↑(A ∩ (↑H + {x₀})) := by
    calc
      (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ)
      _ ≤ Nat.card (A + A) := by
        gcongr; exact Nat.card_mono (toFinite _) <| add_subset_add_left inter_subset_left
      _ ≤ K * Nat.card A := hA
      _ = (K ^ 5 * Nat.card A ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
          (K ^ (-4 : ℤ) * Nat.card A ^ (1/2 : ℝ) * (H : Set G).ncard ^ (1/2 : ℝ)) := by
        simp_rw [← rpow_natCast, ← rpow_intCast]; rpow_ring; norm_num
      _ ≤ (K ^ 5 * Nat.card A ^ (1/2 : ℝ) * (H : Set G).ncard ^ (-1/2 : ℝ)) *
        Nat.card ↑(A ∩ (↑H + {x₀})) := by gcongr
  obtain ⟨u, huA, hucard, hAu, -⟩ :=
    Set.ruzsa_covering_add (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne (by convert Z3)
  have A_subset_uH : A ⊆ u + H := by
    grw [hAu, inter_subset_right, add_sub_add_comm, singleton_sub_singleton, _root_.sub_self]
    simp
  exact ⟨H, u, hucard, IHA, IAH, A_subset_uH⟩

/-- If $A \subset {\bf F}_2^n$ is finite non-empty with $|A+A| \leq K|A|$, then there exists a
subgroup $H$ of ${\bf F}_2^n$ with $|H| \leq |A|$ such that $A$ can be covered by at most $2K^9$
translates of $H$. -/
lemma better_PFR_conjecture {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c < 2 * K ^ 9 ∧ (H : Set G).ncard ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' (Set.toFinite _) h₀A hA
  -- consider the subgroup `H` given by Lemma `PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (-1 / 2 : ℝ)
      ∧ (H : Set G).ncard ≤ K ^ 8 * Nat.card A ∧ Nat.card A ≤ K ^ 8 * (H : Set G).ncard
      ∧ A ⊆ c + H :=
    better_PFR_conjecture_aux h₀A hA
  have H_pos : (0 : ℝ) < (H : Set G).ncard := by
    have : 0 < (H : Set G).ncard := Nat.card_pos; positivity
  rcases le_or_gt ((H : Set G).ncard) (Nat.card A) with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (-1 / 2 : ℝ) := hc
    _ ≤ K ^ 5 * (K ^ 8 * (H : Set G).ncard) ^ (1 / 2 : ℝ) * (H : Set G).ncard ^ (-1 / 2 : ℝ) := by
      gcongr
    _ = K ^ 9 := by simp_rw [← rpow_natCast]; rpow_ring; norm_num
    _ < 2 * K ^ 9 := by linarith [show 0 < K ^ 9 by positivity]
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / 2 < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : Submodule (ZMod 2) G, Nat.card H' ≤ Nat.card A
          ∧ Nat.card A < 2 * Nat.card H' ∧ H' ≤ H := by
      have A_pos' : 0 < Nat.card A := mod_cast A_pos
      exact ZModModule.exists_submodule_subset_card_le Nat.prime_two H h.le A_pos'.ne'
    have : (Nat.card A / 2 : ℝ) < Nat.card H' := by
      rw [div_lt_iff₀ zero_lt_two, mul_comm]; norm_cast
    have H'_pos : (0 : ℝ) < Nat.card H' := by
      have : 0 < Nat.card H' := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ :=
      H'.toAddSubgroup.exists_left_transversal_of_le (H := H.toAddSubgroup) H'H
    dsimp at HH'u
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast natCard_add_le
    _ ≤ (K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * ((H : Set G).ncard ^ (-1 / 2 : ℝ)))
          * ((H : Set G).ncard / Nat.card H') := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * ((H : Set G).ncard ^ (-1 / 2 : ℝ)))
          * ((H : Set G).ncard / (Nat.card A / 2)) := by
        gcongr
    _ = (K ^ 5 * Nat.card A ^ (1 / 2 : ℝ) * ((H : Set G).ncard ^ (-1 / 2 : ℝ)))
          * ((H : Set G).ncard * (Nat.card A : ℝ)⁻¹ * 2) := by
        field_simp
    _ = 2 * K ^ 5 * Nat.card A ^ (-1 / 2 : ℝ) * (H : Set G).ncard ^ (1 / 2 : ℝ) := by
        rpow_ring
        field_simp
        norm_num
    _ ≤ 2 * K ^ 5 * Nat.card A ^ (-1 / 2 : ℝ) * (K ^ 8 * Nat.card A) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = 2 * K ^ 9 := by
        simp_rw [← rpow_natCast]
        rpow_ring
        norm_num

/-- Corollary of `better_PFR_conjecture` in which the ambient group is not required to be finite
(but) then $H$ and $c$ are finite. -/
theorem better_PFR_conjecture' {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (Afin : A.Finite)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 9 ∧ (H : Set G).ncard ≤ Nat.card A ∧ A ⊆ c + H := by
  let G' := Submodule.span (ZMod 2) A
  let G'fin : Fintype G' := (Afin.submoduleSpan _).fintype
  let ι : G'→ₗ[ZMod 2] G := G'.subtype
  have ι_inj : Injective ι := G'.toAddSubgroup.subtype_injective
  let A' : Set G' := ι ⁻¹' A
  have A_rg : A ⊆ range ι := by
    simp only [Submodule.coe_subtype, Subtype.range_coe_subtype, G', ι]
    exact Submodule.subset_span
  have cardA' : Nat.card A' = Nat.card A := Nat.card_preimage_of_injective ι_inj A_rg
  have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
    rwa [cardA', ← preimage_add _ ι_inj A_rg A_rg,
         Nat.card_preimage_of_injective ι_inj (add_subset_range _ A_rg A_rg)]
  rcases better_PFR_conjecture (h₀A.preimage' A_rg) hA' with ⟨H', c', hc', hH', hH'₂⟩
  refine ⟨H'.map ι , ι '' c', toFinite _, toFinite (ι '' H'), ?_, ?_, fun x hx ↦ ?_⟩
  · rwa [Nat.card_image_of_injective ι_inj]
  · simpa [Set.ncard_image_of_injective _ ι_inj, ← cardA']
  · erw [← image_add]
    exact ⟨⟨x, Submodule.subset_span hx⟩, hH'₂ hx, rfl⟩

end PFR
