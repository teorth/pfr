module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import PFR.ForMathlib.Entropy.Group
public import PFR.ForMathlib.Entropy.Kernel.RuzsaDist
public import PFR.ForMathlib.FiniteRange.IdentDistrib
public import PFR.Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Ruzsa distance

Here we define Ruzsa distance and establish its basic properties.

## Main definitions

* `rdist`: The Ruzsa distance $d[X ; Y]$ between two random variables
* `condRuzsaDist`: The conditional Ruzsa distance $d[X | Z ; Y | W]$ (or $d[X ; Y | W]$) between two
  random variables, conditioned on additional random variables

## Main results

* `rdist_triangle`: The Ruzsa triangle inequality for three random variables.
* `kaimanovich_vershik`. $$H[X + Y + Z] - H[X + Y] \leq H[Y+ Z] - H[Y]$$
* `ent_bsg`: If $Z=A+B$, then
  $$\sum_{z} P[Z=z] d[(A | Z = z) ; (B | Z = z)] \leq 3 I[A :B] + 2 H[Z] - H[A] - H[B]$$
-/

@[expose] public section

open Filter Function MeasureTheory Measure ProbabilityTheory
open scoped Topology

variable {Ω Ω' Ω'' Ω''' G S T : Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G]

/-- Entropy depends continuously on the measure. -/
-- TODO: Use notation `Hm[μ]` here? (figure out how)
lemma continuous_measureEntropy_probabilityMeasure {Ω : Type*} [Finite Ω]
    [TopologicalSpace Ω] [DiscreteTopology Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] :
    Continuous (fun (μ : ProbabilityMeasure Ω) ↦ measureEntropy (S := Ω) μ) := by
  cases nonempty_fintype Ω
  unfold measureEntropy
  simp_rw [tsum_fintype]
  apply continuous_finset_sum
  intro ω _
  apply Real.continuous_negMulLog.comp
  simp only [measure_univ, inv_one, one_smul]
  exact continuous_probabilityMeasure_apply_of_isClopen (s := {ω}) <| isClopen_discrete _

lemma continuous_entropy_restrict_probabilityMeasure [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] :
    Continuous (fun (μ : ProbabilityMeasure G) ↦ H[id ; μ.toMeasure]) := by
  simp only [entropy_def, Measure.map_id]
  exact continuous_measureEntropy_probabilityMeasure

variable [AddCommGroup G]
  {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}

/-- The Ruzsa distance `rdist X Y` or `d[X ; Y]` between two random variables is defined as
`H[X'- Y'] - H[X']/2 - H[Y']/2`, where `X', Y'` are independent copies of `X, Y`. -/
noncomputable
def rdist (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  H[fun x ↦ x.1 - x.2 ; (μ.map X).prod (μ'.map Y)] - H[X ; μ]/2 - H[Y ; μ']/2

/- Needed a new separator here, chose `#` arbitrarily, but am open to other suggestions -/
@[inherit_doc rdist] notation3:max "d[" X "; " μ " # " Y "; " μ' "]" => rdist X Y μ μ'

@[inherit_doc rdist] notation3:max "d[" X " # " Y "]" => rdist X Y volume volume

/-- Explicit formula for the Ruzsa distance. -/
lemma rdist_def (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω) (μ' : Measure Ω') :
    d[X ; μ # Y ; μ']
      = H[fun x ↦ x.1 - x.2 ; (μ.map X).prod (μ'.map Y)] - H[X ; μ]/2 - H[Y ; μ']/2 := rfl

/-- Ruzsa distance of random variables equals Ruzsa distance of the kernels. -/
lemma rdist_eq_rdistm : d[X ; μ # Y ; μ'] = Kernel.rdistm (μ.map X) (μ'.map Y) := rfl

/-- Ruzsa distance depends continuously on the measure. -/
lemma continuous_rdist_restrict_probabilityMeasure [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] :
    Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦
        d[id ; μ.1.toMeasure # id ; μ.2.toMeasure]) := by
  simp [rdist_def]
  have obs₀ : Continuous (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦
      H[fun x ↦ x.1 - x.2 ; μ.1.toMeasure.prod μ.2.toMeasure]) := by
    simp_rw [entropy_def]
    have diff_cts : Continuous (fun (x : G × G) ↦ x.1 - x.2) := by continuity
    have key₁ := ProbabilityMeasure.continuous_prod (α := G) (β := G)
    have key₂ := ProbabilityMeasure.continuous_map diff_cts
    convert continuous_measureEntropy_probabilityMeasure.comp (key₂.comp key₁)
  have obs₁ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ H[id ; μ.1.toMeasure]) := by
    convert (continuous_measureEntropy_probabilityMeasure (Ω := G)).comp continuous_fst
    simp [entropy_def]
  have obs₂ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ H[id ; μ.2.toMeasure]) := by
    convert (continuous_measureEntropy_probabilityMeasure (Ω := G)).comp continuous_snd
    simp [entropy_def]
  continuity

lemma continuous_rdist_restrict_probabilityMeasure₁ [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    (X : Ω → G) (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] (X_mble : Measurable X) :
    Continuous
      (fun (μ : ProbabilityMeasure G) ↦ d[id ; P.map X # id ; μ.toMeasure]) := by
  have obs : IsProbabilityMeasure (P.map X) := by
    refine ⟨by simp [Measure.map_apply X_mble MeasurableSet.univ]⟩
  let ι : ProbabilityMeasure G → ProbabilityMeasure G × ProbabilityMeasure G :=
      fun ν ↦ ⟨⟨P.map X, obs⟩, ν⟩
  have ι_cont : Continuous ι := Continuous.prodMk_right _
  convert continuous_rdist_restrict_probabilityMeasure.comp ι_cont

/-- Ruzsa distance between random variables equals Ruzsa distance between their distributions. -/
lemma rdist_eq_rdist_id_map : d[X ; μ # Y ; μ'] = d[id ; μ.map X # id ; μ'.map Y] := by
  simp only [rdist_def, entropy_def, Measure.map_id]

/-- Ruzsa distance depends continuously on the second measure. -/
lemma continuous_rdist_restrict_probabilityMeasure₁' [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    (X : Ω → G) (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] (X_mble : Measurable X) :
    Continuous
      (fun (μ : ProbabilityMeasure G) ↦ d[X ; P # id ; μ.toMeasure]) := by
  simp only [@rdist_eq_rdist_id_map Ω G G mΩ P hG, Measure.map_id]
  exact continuous_rdist_restrict_probabilityMeasure₁ _ _ X_mble

/-- If `X', Y'` are copies of `X, Y` respectively then `d[X' ; Y'] = d[X ; Y]`. -/
lemma ProbabilityTheory.IdentDistrib.rdist_congr {X' : Ω'' → G} {Y' : Ω''' → G}
    (hX : IdentDistrib X X' μ μ'') (hY : IdentDistrib Y Y' μ' μ''') :
    d[X ; μ # Y ; μ'] = d[X' ; μ'' # Y' ; μ'''] := by
  simp [rdist, hX.map_eq, hY.map_eq, hX.entropy_congr, hY.entropy_congr]

/-- If `X', Y'` are copies of `X, Y` respectively then `d[X' ; Y'] = d[X ; Y]`. -/
lemma ProbabilityTheory.IdentDistrib.rdist_congr_left {X' : Ω'' → G}
    (hY : AEMeasurable Y μ') (hX : IdentDistrib X X' μ μ'') :
    d[X ; μ # Y ; μ'] = d[X' ; μ'' # Y ; μ'] := hX.rdist_congr <| .refl hY

/-- If `X', Y'` are copies of `X, Y` respectively then `d[X' ; Y'] = d[X ; Y]`. -/
lemma ProbabilityTheory.IdentDistrib.rdist_congr_right {Y' : Ω''' → G}
    (hX : AEMeasurable X μ) (hY : IdentDistrib Y Y' μ' μ''') :
    d[X ; μ # Y ; μ'] = d[X ; μ # Y' ; μ'''] := (IdentDistrib.refl hX).rdist_congr hY

lemma tendsto_rdist_probabilityMeasure {α : Type*} {l : Filter α}
    [TopologicalSpace Ω] [BorelSpace Ω] [TopologicalSpace G] [BorelSpace G] [Finite G]
    [DiscreteTopology G]
    {X Y : Ω → G} (hX : Continuous X) (hY : Continuous Y)
    {μ : α → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω} (hμ : Tendsto μ l (𝓝 ν)) :
    Tendsto (fun n ↦ d[X ; (μ n : Measure Ω) # Y ; (μ n : Measure Ω)]) l
      (𝓝 (d[X ; ν # Y ; ν])) := by
  have J (η : ProbabilityMeasure Ω) :
      d[X ; η # Y ; η] = d[(id : G → G) ; η.map hX.aemeasurable # id ; η.map hY.aemeasurable] := by
    apply ProbabilityTheory.IdentDistrib.rdist_congr
    · exact ⟨hX.aemeasurable, aemeasurable_id, by simp⟩
    · exact ⟨hY.aemeasurable, aemeasurable_id, by simp⟩
  simp_rw [J]
  have Z := ((continuous_rdist_restrict_probabilityMeasure (G := G)).tendsto
    ((ν.map hX.aemeasurable), (ν.map hY.aemeasurable)))
  have T : Tendsto (fun n ↦ (((μ n).map hX.aemeasurable), ((μ n).map hY.aemeasurable)))
      l (𝓝 (((ν.map hX.aemeasurable), (ν.map hY.aemeasurable)))) := by
    apply Tendsto.prodMk_nhds
    · exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hμ hX
    · exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hμ hY
  apply Z.comp T

section rdist

variable [Countable G] [MeasurableSingletonClass G]

/-- If `X, Y` are independent `G`-random variables then `d[X ; Y] = H[X - Y] - H[X]/2 - H[Y]/2`. -/
lemma ProbabilityTheory.IndepFun.rdist_eq [IsFiniteMeasure μ]
    {Y : Ω → G} (h : IndepFun X Y μ) (hX : Measurable X) (hY : Measurable Y) :
    d[X ; μ # Y ; μ] = H[X - Y ; μ] - H[X ; μ]/2 - H[Y ; μ]/2 := by
  rw [rdist_def]
  congr 2
  have h_prod : (μ.map X).prod (μ.map Y) = μ.map (⟨X, Y⟩) :=
    ((indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp h).symm
  rw [h_prod, entropy_def, Measure.map_map (measurable_fst.sub measurable_snd) (hX.prodMk hY)]
  rfl

/-- `d[X ; Y] ≤ H[X]/2 + H[Y]/2`. -/
lemma rdist_le_avg_ent {X : Ω → G} {Y : Ω' → G} [FiniteRange X] [FiniteRange Y] (hX : Measurable X)
    (hY : Measurable Y) (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    d[X ; μ # Y ; μ'] ≤ (H[X ; μ] + H[Y ; μ'])/2 := by
  rcases ProbabilityTheory.independent_copies_finiteRange hX hY μ μ'
    with ⟨ν, X', Y', hprob, hX', hY', h_indep, hidentX, hidentY, hfinX, hfinY⟩
  rw [← hidentX.rdist_congr hidentY,
    ← hidentX.entropy_congr, ← IdentDistrib.entropy_congr hidentY,
    h_indep.rdist_eq hX' hY']
  suffices H[X' - Y'; ν] ≤ H[X'; ν] + H[Y'; ν] by linarith
  change H[(fun x ↦ x.1 - x.2) ∘ ⟨X',Y' ⟩; ν] ≤ H[X'; ν] + H[Y'; ν]
  exact ((entropy_comp_le ν (by fun_prop) _).trans) (entropy_pair_le_add hX' hY' ν)

/-- Applying an injective homomorphism does not affect Ruzsa distance. -/
lemma rdist_of_inj {H : Type*} [hH : MeasurableSpace H] [MeasurableSingletonClass H]
  [AddCommGroup H] [Countable H] (hX : Measurable X) (hY : Measurable Y)
  (φ : G →+ H) (hφ : Injective φ) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    d[φ ∘ X ; μ # φ ∘ Y ; μ'] = d[X ; μ # Y ; μ'] := by
    rw [rdist_def, rdist_def]
    congr 2
    · rw [← entropy_comp_of_injective _ (by fun_prop) _ hφ]
      apply IdentDistrib.entropy_congr
      constructor
      · exact Measurable.aemeasurable .of_discrete
      · exact Measurable.aemeasurable .of_discrete
      set g := fun x : H × H ↦ x.1 - x.2
      set f := fun x : G × G ↦ (φ x.1, φ x.2)
      have : φ ∘ (fun x ↦ x.1 - x.2) = g ∘ f := by ext; simp [f, g]
      rw [this, ← Measure.map_map (g := g) (f := f) .of_discrete
        .of_discrete, ← Measure.map_map .of_discrete hX,
        ← Measure.map_map .of_discrete hY]
      congr
      convert Measure.map_prod_map _ _ .of_discrete .of_discrete
      · exact instSFiniteMap μ X
      · exact instSFiniteMap μ' Y
      all_goals infer_instance
    · congr 1
      exact entropy_comp_of_injective _ hX _ hφ
    exact entropy_comp_of_injective _ hY _ hφ

/-- `d[X ; 0] = H[X] / 2`. -/
lemma rdist_zero_eq_half_ent [IsFiniteMeasure μ] [IsProbabilityMeasure μ'] :
    d[X ; μ # fun _ ↦ 0 ; μ'] = H[X ; μ]/2 := by
  have aux : H[fun x => x.1 - x.2 ; (μ.map X).prod (dirac 0)]
            = H[X ; μ] := by
    have h : ((μ.map X).prod (dirac 0)).map (fun x => x.1 - x.2) = Measure.map X μ := by
      rw [Measure.prod_dirac, Measure.map_map (by fun_prop) (by fun_prop)]
      simp [Function.comp_def]
    simp [entropy_def, h]
  simp [rdist_def, entropy_const (0 : G), aux]
  ring

/-- `d[X ; Y] = d[Y ; X]` -/
lemma rdist_symm [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    d[X ; μ # Y ; μ'] = d[Y ; μ' # X ; μ] := by
  rw [rdist_def, rdist_def, sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_neg (measurable_fst.sub measurable_snd)]
  have : (-fun x : G × G ↦ x.1 - x.2) = (fun x ↦ x.1 - x.2) ∘ Prod.swap := by ext ; simp
  rw [this, entropy_def, ← Measure.map_map (measurable_fst.sub measurable_snd) measurable_swap,
    Measure.prod_swap]
  rfl

omit [Countable G] in
/-- Ruzsa distance depends continuously on the first measure. -/
lemma continuous_rdist_restrict_probabilityMeasure₁_left [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    (X : Ω → G) (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] (X_mble : Measurable X) :
    Continuous
      (fun (μ : ProbabilityMeasure G) ↦ d[id ; μ.toMeasure # X ; P]) := by
  convert continuous_rdist_restrict_probabilityMeasure₁' X P X_mble using 2
  rw [rdist_symm]

variable [FiniteRange X] [FiniteRange Y]

/-- `|H[X] - H[Y]| ≤ 2 d[X ; Y]`. -/
lemma diff_ent_le_rdist [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) :
    |H[X ; μ] - H[Y ; μ']| ≤ 2 * d[X ; μ # Y ; μ'] := by
  obtain ⟨ν, X', Y', _, hX', hY', hind, hIdX, hIdY, _, _⟩ :=
    independent_copies_finiteRange hX hY μ μ'
  rw [← hIdX.rdist_congr hIdY, hind.rdist_eq hX' hY', ← hIdX.entropy_congr, ← hIdY.entropy_congr,
    abs_le]
  have := max_entropy_le_entropy_sub hX' hY' hind
  constructor
  · linarith[le_max_right H[X'; ν] H[Y'; ν]]
  · linarith[le_max_left H[X'; ν] H[Y'; ν]]

/-- `H[X - Y] - H[X] ≤ 2d[X ; Y]`. -/
lemma diff_ent_le_rdist' [IsProbabilityMeasure μ] {Y : Ω → G}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) [FiniteRange Y] :
    H[X - Y ; μ] - H[X ; μ] ≤ 2 * d[X ; μ # Y ; μ] := by
  rw [h.rdist_eq hX hY]
  linarith[max_entropy_le_entropy_sub hX hY h, le_max_right H[X ; μ] H[Y; μ]]

/-- `H[X - Y] - H[Y] ≤ 2d[X ; Y]`. -/
lemma diff_ent_le_rdist'' [IsProbabilityMeasure μ] {Y : Ω → G}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) [FiniteRange Y] :
    H[X - Y ; μ] - H[Y ; μ] ≤ 2 * d[X ; μ # Y ; μ] := by
  rw [h.rdist_eq hX hY]
  linarith[max_entropy_le_entropy_sub hX hY h, le_max_left H[X ; μ] H[Y; μ]]

/-- `d[X ; Y] ≥ 0`. -/
lemma rdist_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) : 0 ≤ d[X ; μ # Y ; μ'] := by
  linarith [ge_trans (diff_ent_le_rdist hX hY) (abs_nonneg (H[X ; μ] - H[Y ; μ']))]

/-- If $G$ is an additive group and $X$ is a $G$-valued random variable and
$H\leq G$ is a finite subgroup then, with $\pi:G\to G/H$ the natural homomorphism we have
(where $U_H$ is uniform on $H$) $\mathbb{H}(\pi(X))\leq 2d[X;U_H].$ -/
lemma ent_of_proj_le {UH : Ω' → G} [FiniteRange UH]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hU : Measurable UH) {H : AddSubgroup G} (hH : Set.Finite (H : Set G))
    -- TODO: infer from [FiniteRange UH]?
    (hunif : IsUniform H UH μ') :
    H[(QuotientAddGroup.mk' H) ∘ X; μ] ≤ 2 * d[X; μ # UH ; μ'] := by
  obtain ⟨ν, X', UH', hν, hX', hUH', h_ind, h_id_X', h_id_UH', _, _⟩ :=
    independent_copies_finiteRange hX hU μ μ'
  replace hunif : IsUniform H UH' ν :=
    IsUniform.of_identDistrib hunif h_id_UH'.symm .of_discrete
  rewrite [← (h_id_X'.comp (by fun_prop)).entropy_congr, ← h_id_X'.rdist_congr h_id_UH']
  let π := ⇑(QuotientAddGroup.mk' H)
  let νq := Measure.map (π ∘ X') ν
  have : Countable (HasQuotient.Quotient G H) := Quotient.countable
  have : MeasurableSingletonClass (HasQuotient.Quotient G H) :=
    { measurableSet_singleton := fun _ ↦ measurableSet_quotient.mpr .of_discrete }
  have : Finite H := hH
  have : H[X' - UH' | π ∘ X' ; ν] = H[UH' ; ν] := by
    have h_meas_le : ∀ y ∈ FiniteRange.toFinset (π ∘ X'),
        νq.real {y} * H[X' - UH' | (π ∘ X') ← y ; ν] ≤ νq.real {y} * H[UH' ; ν] := by
      intro x _
      gcongr
      let ν' := ν[|π ∘ X' ← x]
      let π' := QuotientAddGroup.mk (s := H)
      have h_card : (π' ⁻¹' {x}).ncard = Nat.card H := Nat.card_congr <|
        (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet H _).trans <| Equiv.prodUnique H _
      have : Finite (π' ⁻¹' {x}) :=
        Nat.finite_of_card_ne_zero <| h_card.trans_ne <| Nat.pos_iff_ne_zero.mp (Nat.card_pos)
      convert entropy_le_log_card_of_mem_finite this (hX'.sub hUH') ?_
      · simp [hunif.entropy_eq' hH hUH', h_card]
        simp [← Nat.card_coe_set_eq]
      let T : Set (G × G) := ((π' ∘ X') ⁻¹' {x})ᶜ
      let U : Set (G × G) := UH' ⁻¹' Hᶜ
      have h_subset : (X' - UH') ⁻¹' (π' ⁻¹' {x})ᶜ ⊆ T ∪ U :=
        fun ω hω ↦ Classical.byContradiction fun h ↦ by simp_all [not_or, T, U, π']
      refine mem_ae_iff.mpr (nonpos_iff_eq_zero.mp ?_)
      calc
        _ ≤ ν' T + ν' U := (measure_mono h_subset).trans (measure_union_le T U)
        _ = ν' T + 0 := congrArg _ <| by
          simp only [ν', ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
          rw [nonpos_iff_eq_zero.mp <|
            (restrict_apply_le _ U).trans_eq hunif.measure_preimage_compl, mul_zero]
        _ = 0 := by
          have : restrict ν (π ∘ X' ⁻¹' {x}) T = 0 := by
            simp [restrict_apply .of_discrete, T, π', π]
          simp only [ν', ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
          simp [this]
    have h_one : ∑ x ∈ FiniteRange.toFinset (π ∘ X'), νq.real {x} = 1 := by
      rewrite [sum_measureReal_singleton]
      apply (ENNReal.toReal_eq_one_iff _).mpr
      have := isProbabilityMeasure_map (μ := ν) <| .of_discrete (f := π ∘ X')
      rewrite [← measure_univ (μ := νq), ← FiniteRange.range]
      let rng := Set.range (π ∘ X')
      have h_compl : νq rngᶜ = 0 := ae_map_mem_range (π ∘ X') .of_discrete ν
      rw [← measure_add_measure_compl (MeasurableSet.of_discrete (s := rng)),
        h_compl, add_zero]
    have := FiniteRange.sub X' UH'
    have h_ge : H[X' - UH' | π ∘ X' ; ν] ≥ H[UH' ; ν] := calc
      _ ≥ H[X' - UH' | X' ; ν] := condEntropy_comp_ge ν hX' (hX'.sub hUH') π
      _ = H[UH' | X' ; ν] := condEntropy_sub_left hUH' hX'
      _ = H[UH' ; ν] := h_ind.symm.condEntropy_eq_entropy hUH' hX'
    have h_le : H[X' - UH' | π ∘ X' ; ν] ≤ H[UH' ; ν] := by
      rewrite [condEntropy_eq_sum _ _ _ .of_discrete]
      apply (Finset.sum_le_sum h_meas_le).trans
      rewrite [← Finset.sum_mul, h_one, one_mul]
      rfl
    exact h_le.ge_iff_eq.mp h_ge
  have : H[X' - UH' ; ν] = H[π ∘ X' ; ν] + H[UH' ; ν] := by calc
    _ = H[⟨X' - UH', π ∘ (X' - UH')⟩ ; ν] := (entropy_prod_comp (hX'.sub hUH') ν π).symm
    _ = H[⟨X' - UH', π ∘ X'⟩ ; ν] := by
      apply IdentDistrib.entropy_congr <| IdentDistrib.of_ae_eq (Measurable.aemeasurable
        .of_discrete) <| mem_ae_iff.mpr _
      convert hunif.measure_preimage_compl
      ext; simp [π]
    _ = H[π ∘ X' ; ν] + H[UH' ; ν] := by
      rewrite [chain_rule ν (by exact hX'.sub hUH') .of_discrete]
      congr
  have : d[X' ; ν # UH' ; ν] = H[π ∘ X' ; ν] + (H[UH' ; ν] - H[X' ; ν]) / 2 := by
    rewrite [h_ind.rdist_eq hX' hUH']
    linarith only [this]
  linarith only [this, (abs_le.mp (diff_ent_le_rdist hX' hUH' (μ := ν) (μ' := ν))).2]

/-- Adding a constant to a random variable does not change the Rusza distance. -/
lemma rdist_add_const [IsZeroOrProbabilityMeasure μ] [IsZeroOrProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) {c} :
    d[X ; μ # Y + fun _ ↦ c; μ'] = d[X ; μ # Y ; μ'] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [rdist_def, entropy_add_const hY]
  rcases eq_zero_or_isProbabilityMeasure μ' with rfl | hμ'
  · simp [rdist_def]
  obtain ⟨ν, X', Y', _, hX', hY', hind, hIdX, hIdY, -⟩ := independent_copies_finiteRange hX hY μ μ'
  have A : IdentDistrib (Y' + fun _ ↦ c) (Y + fun _ ↦ c) ν μ' := by
    change IdentDistrib (fun ω ↦ Y' ω + c) (fun ω ↦ Y ω + c) ν μ'
    apply hIdY.comp (measurable_add_const c)
  have B : IndepFun X' (Y' + fun _ ↦ c) ν := by
    change IndepFun X' (fun ω ↦ Y' ω + c) ν
    apply hind.comp measurable_id (measurable_add_const c)
  have C : X' - (Y' + fun _ ↦ c) = (X' - Y') + (fun _ ↦ -c) := by
    ext ω; simp; abel
  rw [← hIdX.rdist_congr hIdY, ← hIdX.rdist_congr A, hind.rdist_eq hX' hY',
    B.rdist_eq hX' (hY'.add_const _), entropy_add_const hY' c, C, entropy_add_const]
  exact hX'.sub hY'

/-- A variant of `rdist_add_const` where one adds constants to both variables. -/
lemma rdist_add_const' [IsZeroOrProbabilityMeasure μ] [IsZeroOrProbabilityMeasure μ']
    (c : G) (c' : G) (hX : Measurable X) (hY : Measurable Y) :
    d[X + fun _ ↦ c; μ # Y + fun _ ↦ c'; μ'] = d[X ; μ # Y ; μ'] := by
  rw [rdist_add_const _ hY, rdist_symm, rdist_add_const hY hX, rdist_symm]
  fun_prop

/-- The **improved entropic Ruzsa triangle inequality**. -/
lemma ent_of_diff_le (X : Ω → G) (Y : Ω → G) (Z : Ω → G)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : IndepFun (⟨X, Y⟩) Z μ)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[X - Y; μ] ≤ H[X - Z; μ] + H[Z - Y; μ] - H[Z; μ] := by
  have h1 : H[⟨X - Z, ⟨Y, X - Y⟩⟩; μ] + H[X - Y; μ] ≤ H[⟨X - Z, X - Y⟩; μ] + H[⟨Y, X - Y⟩; μ] :=
    entropy_triple_add_entropy_le μ (hX.sub hZ) hY (hX.sub hY)
  have h2 : H[⟨X - Z, X - Y⟩ ; μ] ≤ H[X - Z ; μ] + H[Y - Z ; μ] := by
    calc H[⟨X - Z, X - Y⟩ ; μ] ≤ H[⟨X - Z, Y - Z⟩ ; μ] := by
          have : ⟨X - Z, X - Y⟩ = (fun p ↦ (p.1, p.1 - p.2)) ∘ ⟨X - Z, Y - Z⟩ := by ext1; simp
          rw [this]
          apply entropy_comp_le μ (by fun_prop)
    _ ≤ H[X - Z ; μ] + H[Y - Z ; μ] := by
          have h : 0 ≤ H[X - Z ; μ] + H[Y - Z ; μ] - H[⟨X - Z, Y - Z⟩ ; μ] := by
            apply mutualInfo_nonneg (by fun_prop) (by fun_prop) μ
          linarith
  have h3 : H[⟨Y, X - Y⟩ ; μ] ≤ H[⟨X, Y⟩ ; μ] := by
    have : ⟨Y, X - Y⟩ = (fun p ↦ (p.2, p.1 - p.2)) ∘ ⟨X, Y⟩ := by ext1; simp
    rw [this]
    exact entropy_comp_le μ (hX.prodMk hY) _
  have h4 : H[⟨X - Z, ⟨Y, X - Y⟩⟩; μ] = H[⟨X, ⟨Y, Z⟩⟩ ; μ] := by
    refine entropy_of_comp_eq_of_comp μ ((hX.sub hZ).prodMk (hY.prodMk (hX.sub hY)))
      (hX.prodMk (hY.prodMk hZ))
      (fun p : G × (G × G) ↦ (p.2.2 + p.2.1, p.2.1, -p.1 + p.2.2 + p.2.1))
      (fun p : G × G × G ↦ (p.1 - p.2.2, p.2.1, p.1 - p.2.1)) ?_ ?_
    · ext1; simp
    · ext1; simp
  have h5 : H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨X, Y⟩ ; μ] + H[Z ; μ] := by
    rw [entropy_assoc hX hY hZ, entropy_pair_eq_add (hX.prodMk hY) hZ]
    exact h
  rw [h4, h5] at h1
  calc H[X - Y; μ] ≤ H[X - Z; μ] + H[Y - Z; μ] - H[Z; μ] := by linarith
  _ = H[X - Z; μ] + H[Z - Y; μ] - H[Z; μ] := by
    congr 2
    rw [entropy_sub_comm hY hZ]

/-- The **entropic Ruzsa triangle inequality** -/
lemma rdist_triangle {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [hμ : IsProbabilityMeasure μ] [hμ' : IsProbabilityMeasure μ']
    [hμ'' : IsProbabilityMeasure μ''] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    d[X ; μ # Z ; μ''] ≤ d[X ; μ # Y ; μ'] + d[Y ; μ' # Z ; μ''] := by
  obtain ⟨A, mA, μA, X', Y', Z', hμA, hInd, hX', hY', hZ', HX, HY, HZ, _, _, _⟩ :=
    independent_copies3_nondep_finiteRange hX hY hZ μ μ' μ''
  suffices d[X' ; μA # Z' ; μA] ≤ d[X' ; μA # Y' ; μA] + d[Y' ; μA # Z' ; μA] by
    rwa [HX.rdist_congr HY, HY.rdist_congr HZ, HX.rdist_congr HZ] at this
  have IndepLem : IndepFun (⟨X', Z'⟩) Y' μA :=
    iIndepFun.indepFun_prodMk hInd (fun i => by fin_cases i ; all_goals { simpa }) 0 2 1
      (by norm_cast) (by norm_cast)
  calc d[X' ; μA # Z' ; μA] = H[X' - Z'; μA] - (H[X'; μA] / 2 + H[Z'; μA] / 2) := by
        rw [ProbabilityTheory.IndepFun.rdist_eq
          (by simpa using hInd.indepFun (show 0 ≠ 2 by norm_cast)) hX' hZ'] ; ring
    _ ≤ (H[X' - Y' ; μA] + H[Y' - Z' ; μA] - H[Y' ; μA]) - (H[X'; μA] / 2 + H[Z'; μA] / 2) :=
          sub_le_sub_right (ent_of_diff_le _ _ _ hX' hZ' hY' IndepLem) _
    _ = (H[X' - Y' ; μA] - H[X'; μA] / 2 - H[Y' ; μA] / 2) +
          (H[Y' - Z' ; μA] - H[Y' ; μA] / 2 - H[Z'; μA] / 2) := by ring
    _ = d[X' ; μA # Y' ; μA] + d[Y' ; μA # Z' ; μA] := by
        rw [ProbabilityTheory.IndepFun.rdist_eq (by simpa using (iIndepFun.indepFun hInd
          (show 0 ≠ 1 by norm_cast))) hX' hY', ProbabilityTheory.IndepFun.rdist_eq
          (by simpa using (iIndepFun.indepFun hInd (show 1 ≠ 2 by norm_cast))) hY' hZ']

end rdist

variable [MeasurableSpace S] [MeasurableSpace T] [Countable G] [MeasurableSingletonClass G]

/-- The conditional Ruzsa distance `d[X|Z ; Y|W]`. -/
noncomputable
def condRuzsaDist (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ]
    (μ' : Measure Ω' := by volume_tac) [IsFiniteMeasure μ'] : ℝ :=
  dk[condDistrib X Z μ ; μ.map Z # condDistrib Y W μ' ; μ'.map W]

@[inherit_doc condRuzsaDist]
notation3:max "d[" X " | " Z " ; " μ " # " Y " | " W " ; " μ'"]" => condRuzsaDist X Z Y W μ μ'

@[inherit_doc condRuzsaDist]
notation3:max "d[" X " | " Z " # " Y " | " W "]" => condRuzsaDist X Z Y W volume volume

lemma condRuzsaDist_def (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω) [IsFiniteMeasure μ] (μ' : Measure Ω') [IsFiniteMeasure μ'] :
    d[X | Z ; μ # Y | W ; μ']
      = dk[condDistrib X Z μ ; μ.map Z # condDistrib Y W μ' ; μ'.map W] := rfl

@[simp] lemma condRuszaDist_zero_right (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    d[X | Z ; μ # Y | W ; 0] = 0 := by
  simp only [condRuzsaDist, Measure.map_zero, Kernel.rdist_zero_right]

@[simp] lemma condRuszaDist_zero_left (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ' : Measure Ω') [IsFiniteMeasure μ'] :
    d[X | Z ; 0 # Y | W ; μ'] = 0 := by
  simp [condRuzsaDist]

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

/-- Explicit formula for conditional Ruzsa distance $d[X|Z; Y|W]$ in a fintype. -/
lemma condRuzsaDist_eq_sum' {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T}
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsFiniteMeasure μ] (μ' : Measure Ω') [IsFiniteMeasure μ']
    [Fintype S] [Fintype T] :
    d[X | Z ; μ # Y | W ; μ']
      = ∑ z, ∑ w, μ.real (Z ⁻¹' {z}) * μ'.real (W ⁻¹' {w})
          * d[X ; (μ[|Z ← z]) # Y ; (μ'[|W ← w])] := by
  rw [condRuzsaDist_def, Kernel.rdist, integral_fintype _ .of_finite]
  simp_rw [Measure.prod_real_singleton, smul_eq_mul, Fintype.sum_prod_type,
    map_measureReal_apply hZ (.singleton _), map_measureReal_apply hW (.singleton _)]
  congr with z
  congr with w
  by_cases hz : μ.real (Z ⁻¹' {z}) = 0
  · simp only [mul_eq_mul_left_iff, mul_eq_zero]
    refine .inr <| .inl ?_
    simp [hz]
  by_cases hw : μ'.real (W ⁻¹' {w}) = 0
  · simp only [mul_eq_mul_left_iff, mul_eq_zero]
    refine .inr <| .inr ?_
    simp [hw]
  congr 1
  simp only [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top μ, or_false,
    measure_ne_top] at hz hw
  rw [rdist_eq_rdistm]
  rw [condDistrib_apply hX hZ _ _ hz, condDistrib_apply hY hW _ _ hw]

/-- Explicit formula for conditional Ruzsa distance $d[X|Z; Y|W]$. -/
lemma condRuzsaDist_eq_sum {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T}
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsFiniteMeasure μ] (μ' : Measure Ω') [IsFiniteMeasure μ']
    [FiniteRange Z] [FiniteRange W] :
    d[X | Z ; μ # Y | W ; μ']
      = ∑ z ∈ FiniteRange.toFinset Z, ∑ w ∈ FiniteRange.toFinset W,
        μ.real (Z ⁻¹' {z}) * μ'.real (W ⁻¹' {w})
          * d[X ; (μ[|Z ← z]) # Y ; (μ'[|W ← w])] := by
  have : Measure.prod (μ.map Z) (μ'.map W) ((((FiniteRange.toFinset Z)
      ×ˢ (FiniteRange.toFinset W)) : Finset (S × T)): Set (S × T))ᶜ = 0 := by
    apply Measure.prod_of_full_measure_finset
    all_goals {
      rw [Measure.map_apply ‹_›]
      convert measure_empty (μ := μ)
      simp [← FiniteRange.range]
      measurability
    }
  rw [condRuzsaDist_def, Kernel.rdist, integral_eq_setIntegral this, integral_finset _ _ .finset]
  simp_rw [Measure.prod_real_singleton, smul_eq_mul, Finset.sum_product,
    map_measureReal_apply hZ (.singleton _), map_measureReal_apply hW (.singleton _)]
  congr with z
  congr with w
  by_cases hz : μ.real (Z ⁻¹' {z}) = 0
  · simp only [mul_eq_mul_left_iff, mul_eq_zero]
    refine Or.inr (Or.inl ?_)
    simp [hz]
  by_cases hw : μ'.real (W ⁻¹' {w}) = 0
  · simp only [mul_eq_mul_left_iff, mul_eq_zero]
    refine Or.inr (Or.inr ?_)
    simp [hw]
  congr 1
  simp only [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top μ, or_false,
    measure_ne_top] at hz hw
  rw [rdist_eq_rdistm, condDistrib_apply hX hZ _ _ hz, condDistrib_apply hY hW _ _ hw]

variable [Countable S]

/-- $$ d[X|Z; Y|W] = d[Y|W; X|Z]$$ -/
lemma condRuzsaDist_symm [Countable T]
    {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T} (hZ : Measurable Z)
    (hW : Measurable W) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [FiniteRange Z]
    [FiniteRange W] :
    d[X | Z ; μ # Y | W ; μ'] = d[Y | W ; μ' # X | Z ; μ] := by
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ'.map W) := isProbabilityMeasure_map hW.aemeasurable
  rw [condRuzsaDist_def, condRuzsaDist_def, Kernel.rdist_symm]

lemma condRuzsaDist_nonneg [Countable T] {X : Ω → G} (hX : Measurable X) [FiniteRange X]
    {Z : Ω → S} (hZ : Measurable Z) [FiniteRange Z]
    {Y : Ω' → G} (hY : Measurable Y) [FiniteRange Y]
    {W : Ω' → T} (hW : Measurable W) [FiniteRange W]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    0 ≤ d[X | Z ; μ # Y | W ; μ'] := by
  rw [condRuzsaDist_def]
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ'.map W) := isProbabilityMeasure_map hW.aemeasurable
  refine Kernel.rdist_nonneg ?_ ?_
  · exact Kernel.aefiniteKernelSupport_condDistrib _ _ _ hX hZ
  · exact Kernel.aefiniteKernelSupport_condDistrib _ _ _ hY hW

/-- The conditional Ruzsa distance `d[X ; Y|W]`. -/
noncomputable
def condRuzsaDist' (X : Ω → G) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) [IsFiniteMeasure μ'] : ℝ :=
  dk[Kernel.const Unit (μ.map X) ; Measure.dirac () # condDistrib Y W μ' ; μ'.map W]

@[inherit_doc condRuzsaDist']
notation3:max "d[" X " ; " μ " # " Y " | " W " ; " μ' "]" => condRuzsaDist' X Y W μ μ'
@[inherit_doc condRuzsaDist']
notation3:max "d[" X " # " Y " | " W "]" => condRuzsaDist' X Y W volume volume

/-- Conditional Ruzsa distance equals Ruzsa distance of associated kernels. -/
lemma condRuzsaDist'_def {T : Type*} [MeasurableSpace T]
    (X : Ω → G) (Y : Ω' → G) (W : Ω' → T) (μ : Measure Ω) (μ' : Measure Ω')
    [IsFiniteMeasure μ'] :
    d[X ; μ # Y | W ; μ'] =
      dk[Kernel.const Unit (μ.map X) ; Measure.dirac () # condDistrib Y W μ' ; μ'.map W] :=
  rfl

@[simp] lemma condRuzsaDist'_zero_right {T : Type*} [MeasurableSpace T]
    (X : Ω → G) (Y : Ω' → G) (W : Ω' → T) (μ : Measure Ω) :
    d[X ; μ # Y | W ; 0] = 0 := by
  simp only [condRuzsaDist'_def, Measure.map_zero, Kernel.rdist_zero_right]

/-- Explicit formula for conditional Ruzsa distance `d[X ; Y | W]`. -/
lemma condRuzsaDist'_eq_sum {X : Ω → G} {Y : Ω' → G} {W : Ω' → T} (hY : Measurable Y)
    (hW : Measurable W) (μ : Measure Ω) (μ' : Measure Ω') [IsFiniteMeasure μ'] [FiniteRange W] :
    d[X ; μ # Y | W ; μ']
      = ∑ w ∈ FiniteRange.toFinset W, μ'.real (W ⁻¹' {w}) * d[X ; μ # Y ; (μ'[|W ← w])] := by
  have : Measure.prod (dirac ()) (μ'.map W) ((Finset.univ (α := Unit) ×ˢ FiniteRange.toFinset W :
    Finset (Unit × T)) : Set (Unit × T))ᶜ = 0 := by
    apply Measure.prod_of_full_measure_finset
    · simp
    rw [Measure.map_apply ‹_› (by measurability)]
    convert measure_empty (μ := μ)
    simp [← FiniteRange.range]
  rw [condRuzsaDist'_def, Kernel.rdist, integral_eq_setIntegral this, integral_finset _ _ .finset]
  simp_rw [Measure.prod_real_singleton, smul_eq_mul, Finset.sum_product]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  simp_rw [map_measureReal_apply hW (.singleton _)]
  congr with w
  by_cases hw : μ'.real (W ⁻¹' {w}) = 0
  · simp [hw]
  rw [rdist_eq_rdistm, condDistrib_apply hY hW _ _]
  · congr
    simp
  · intro h
    simp [h, measureReal_def] at hw

/-- Alternate formula for conditional Ruzsa distance `d[X ; Y | W]` when T is a Fintype. -/
lemma condRuzsaDist'_eq_sum' {X : Ω → G} {Y : Ω' → G} {W : Ω' → T} (hY : Measurable Y)
    (hW : Measurable W) (μ : Measure Ω) (μ' : Measure Ω') [IsFiniteMeasure μ'] [Fintype T] :
    d[X ; μ # Y | W ; μ']
      = ∑ w, μ'.real (W ⁻¹' {w}) * d[X ; μ # Y ; (μ'[|W ← w])] := by
  rw [condRuzsaDist'_eq_sum hY hW μ μ']
  apply Finset.sum_subset
  · simp
  intro w _ hw
  simp only [FiniteRange.mem_iff, not_exists] at hw
  have : W⁻¹' {w} = ∅ := by
    ext ω; simp [hw ω]
  simp [this]

open scoped ENNReal

lemma condRuzsaDist'_prod_eq_sum {X : Ω → G} {Y : Ω' → G} {W W' : Ω' → T}
    (μ : Measure Ω) (μ' : Measure Ω') (hY : Measurable Y) (hW' : Measurable W') (hW : Measurable W)
    [IsFiniteMeasure μ'] [FiniteRange W] [FiniteRange W'] :
    d[X ; μ # Y | ⟨W', W⟩; μ']
      = ∑ w ∈ FiniteRange.toFinset W, μ'.real (W ⁻¹' {w}) * d[X ; μ # Y | W' ; (μ'[|W ← w])] := by
  have : d[X ; μ # Y | ⟨W', W⟩; μ'] = ∑ w ∈ ((FiniteRange.toFinset W') ×ˢ FiniteRange.toFinset W),
    μ'.real ((fun a => (W' a, W a)) ⁻¹' {w}) * d[X; μ # Y; μ'[|(fun a ↦ (W' a, W a)) ⁻¹' {w}]] := by
    rw [condRuzsaDist'_eq_sum hY (hW'.prodMk hW)]
    apply Finset.sum_subset
    · intro (t, t')
      simp only [FiniteRange.mem_iff, Prod.mk.injEq, Finset.mem_product, forall_exists_index,
        and_imp]
      exact fun ω h1 h2 ↦ ⟨⟨ω, h1⟩, ⟨ω, h2⟩⟩
    intro (t, t') _ ht
    simp only [FiniteRange.mem_iff, Prod.mk.injEq, not_exists, not_and] at ht
    have : (fun a => (W' a, W a)) ⁻¹' {(t, t')} = ∅ := by
      ext ω
      simpa using ht ω
    simp [this]
  rw [this, Finset.sum_product_right]
  congr 1 with w
  rw [condRuzsaDist'_eq_sum hY hW', Finset.mul_sum]
  congr 1 with w'
  rw [← mul_assoc]
  have A : (fun a ↦ (W' a, W a)) ⁻¹' {(w', w)} = W' ⁻¹' {w'} ∩ W⁻¹' {w} := by ext; simp
  congr 1
  · simp only [A, ProbabilityTheory.cond_real_apply (hW (.singleton w))]
    obtain hw | hw := eq_or_ne (μ'.real (W ⁻¹' {w})) 0
    · have : μ'.real (W' ⁻¹' {w'} ∩ W ⁻¹' {w}) = 0 :=
        measureReal_mono_null Set.inter_subset_right hw
      simp [hw, this]
    · rw [mul_inv_cancel_left₀ hw, Set.inter_comm]
  · congr 1
    rw [A, cond_cond_eq_cond_inter' (hW (.singleton _)) (hW' (.singleton _)), Set.inter_comm]
    finiteness

/-- Version of `condRuzsaDist'_prod_eq_sum` when `W` has finite codomain. -/
lemma condRuzsaDist'_prod_eq_sum' {X : Ω → G} {Y : Ω' → G} {W W' : Ω' → T}
    (μ : Measure Ω) (μ' : Measure Ω') (hY : Measurable Y) (hW' : Measurable W') (hW : Measurable W)
    [IsFiniteMeasure μ'] [Fintype T] :
    d[X ; μ # Y | ⟨W', W⟩; μ']
      = ∑ w, μ'.real (W ⁻¹' {w}) * d[X ; μ # Y | W' ; (μ'[|W ← w])] := by
  rw [condRuzsaDist'_prod_eq_sum μ μ' hY hW' hW]
  apply Finset.sum_subset
  · simp
  intro w _ hw
  simp only [FiniteRange.mem_iff, not_exists] at hw
  have : W⁻¹' {w} = ∅ := by
    ext ω; simp [hw ω]
  simp [this]

/-- Explicit formula for conditional Ruzsa distance `d[X ; Y | W]`, in integral form. -/
lemma condRuzsaDist'_eq_integral (X : Ω → G) {Y : Ω' → G} {W : Ω' → T}
    (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) (μ' : Measure Ω') [IsFiniteMeasure μ'] [FiniteRange W] :
    d[X ; μ # Y | W ; μ']
      = (μ'.map W)[fun w ↦ d[X ; μ # Y ; (μ'[|W ← w])]] := by
  rw [condRuzsaDist'_eq_sum hY hW]
  simp_rw [← smul_eq_mul]
  have : (μ'.map W) (FiniteRange.toFinset W : Set T)ᶜ = 0 := by
    rw [Measure.map_apply ‹_› (by measurability)]
    convert measure_empty (μ := μ)
    simp [← FiniteRange.range]
  rw [integral_eq_setIntegral this, integral_finset _ _ IntegrableOn.finset]
  simp [map_measureReal_apply hW (MeasurableSet.singleton _),]

section

variable [Countable T]

/-- Conditioning by a constant does not affect Ruzsa distance. -/
lemma condRuzsaDist_of_const {X : Ω → G} (hX : Measurable X)
    (Y : Ω' → G) (W : Ω' → T) (c : S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [FiniteRange W] :
    d[X|(fun _ ↦ c) ; μ # Y | W ; μ'] = d[X ; μ # Y | W ; μ'] := by
  rw [condRuzsaDist_def, condRuzsaDist'_def, Measure.map_const, measure_univ, one_smul,
    Kernel.rdist, Kernel.rdist, integral_prod _ (integrable_of_finiteSupport _), integral_dirac,
    integral_prod _ (integrable_of_finiteSupport _), integral_dirac]
  congr!
  rw [condDistrib_apply hX measurable_const] <;> simp

/-- If `$(X,Z)$` and `$(Y,W)$` are independent, then
`d[X | Z ; Y | W] = H[X'- Y' | Z', W'] - H[X'|Z']/2 - H[Y'|W']/2`. -/
lemma condRuzsaDist_of_indep
    {X : Ω → G} {Z : Ω → S} {Y : Ω → G} {W : Ω → T}
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun (⟨X, Z⟩) (⟨Y, W⟩) μ) [FiniteRange Z] [FiniteRange W] :
    d[X | Z ; μ # Y | W ; μ] = H[X - Y | ⟨Z, W⟩ ; μ] - H[X | Z ; μ]/2 - H[Y | W ; μ]/2 := by
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  rw [condRuzsaDist_def, Kernel.rdist_eq', condEntropy_eq_kernel_entropy _ (hZ.prodMk hW),
    condEntropy_eq_kernel_entropy hX hZ, condEntropy_eq_kernel_entropy hY hW]
  swap; · exact hX.sub hY
  congr 2
  have hZW : IndepFun Z W μ := h.comp measurable_snd measurable_snd
  have hZW_map : μ.map (⟨Z, W⟩) = (μ.map Z).prod (μ.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hW.aemeasurable).mp hZW
  rw [← hZW_map]
  refine Kernel.entropy_congr ?_
  have : Kernel.map (condDistrib (⟨X, Y⟩) (⟨Z, W⟩) μ) (fun x ↦ x.1 - x.2)
      =ᵐ[μ.map (⟨Z, W⟩)] condDistrib (X - Y) (⟨Z, W⟩) μ :=
    (condDistrib_comp _ (by fun_prop) (by fun_prop)).symm
  refine (this.symm.trans ?_).symm
  suffices Kernel.prodMkRight T (condDistrib X Z μ)
        ×ₖ Kernel.prodMkLeft S (condDistrib Y W μ)
      =ᵐ[μ.map (⟨Z, W⟩)] condDistrib (⟨X, Y⟩) (⟨Z, W⟩) μ by
    filter_upwards [this] with x hx
    rw [Kernel.map_apply _ (by fun_prop), Kernel.map_apply _ (by fun_prop), hx]
  exact (condDistrib_eq_prod_of_indepFun hX hZ hY hW μ h).symm

/-- Formula for conditional Ruzsa distance for independent sets of variables. -/
lemma condRuzsaDist'_of_indep {X : Ω → G} {Y : Ω → G} {W : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun X (⟨Y, W⟩) μ) [FiniteRange W] :
    d[X ; μ # Y | W ; μ] = H[X - Y | W ; μ] - H[X ; μ]/2 - H[Y | W ; μ]/2 := by
  have : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  rw [condRuzsaDist'_def, Kernel.rdist_eq', condEntropy_eq_kernel_entropy _ hW,
    condEntropy_eq_kernel_entropy hY hW, entropy_eq_kernel_entropy]
  rotate_left
  · exact hX.sub hY
  congr 2
  let Z : Ω → Unit := fun _ ↦ ()
  rw [← condDistrib_unit_right hX μ]
  have h' : IndepFun (⟨X,Z⟩) (⟨Y, W⟩) μ := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have : ⟨X, Z⟩ ⁻¹' s = X ⁻¹' ((fun c ↦ (c, ())) ⁻¹' s) := by ext1 y; simp
    rw [this]
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
    exact h _ _ (measurable_prodMk_right hs) ht
  have h_indep := condDistrib_eq_prod_of_indepFun hX measurable_const hY hW _ h'
  have h_meas_eq : μ.map (⟨Z, W⟩) = (Measure.dirac ()).prod (μ.map W) := by
    ext s hs
    rw [Measure.map_apply (measurable_const.prodMk hW) hs, Measure.prod_apply hs, lintegral_dirac,
      Measure.map_apply hW (measurable_prodMk_left hs)]
    congr
  rw [← h_meas_eq]
  have : Kernel.map (Kernel.prodMkRight T (condDistrib X Z μ)
        ×ₖ Kernel.prodMkLeft Unit (condDistrib Y W μ)) (fun x ↦ x.1 - x.2)
      =ᵐ[μ.map (⟨Z, W⟩)] Kernel.map (condDistrib (⟨X, Y⟩) (⟨Z, W⟩) μ) (fun x ↦ x.1 - x.2) := by
    filter_upwards [h_indep] with y hy
    conv_rhs => rw [Kernel.map_apply _ (by fun_prop), hy]
    rw [← Kernel.mapOfMeasurable_eq_map _ (by fun_prop)]
    rfl
  rw [Kernel.entropy_congr this]
  have : Kernel.map (condDistrib (⟨X, Y⟩) (⟨Z, W⟩) μ) (fun x ↦ x.1 - x.2)
      =ᵐ[μ.map (⟨Z, W⟩)] condDistrib (X - Y) (⟨Z, W⟩) μ :=
    (condDistrib_comp _ (by fun_prop) (by fun_prop)).symm
  rw [Kernel.entropy_congr this]
  have h_meas : μ.map (⟨Z, W⟩) = (μ.map W).map (Prod.mk ()) := by
    ext s hs
    rw [Measure.map_apply measurable_prodMk_left hs, h_meas_eq, Measure.prod_apply hs,
      lintegral_dirac]
  have h_ker : condDistrib (X - Y) (⟨Z, W⟩) μ
      =ᵐ[μ.map (⟨Z, W⟩)] Kernel.prodMkLeft Unit (condDistrib (X - Y) W μ) := by
    rw [Filter.EventuallyEq, ae_iff_of_countable]
    intro x hx
    rw [Measure.map_apply (measurable_const.prodMk hW) (.singleton _)] at hx
    ext s hs
    have h_preimage_eq : (fun a ↦ (PUnit.unit, W a)) ⁻¹' {x} = W ⁻¹' {x.2} := by
      conv_lhs => rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod]
      ext1 y
      simp
    rw [Kernel.prodMkLeft_apply, condDistrib_apply' _ (measurable_const.prodMk hW) _ _ hx hs,
      condDistrib_apply' _ hW _ _ _ hs]
    rotate_left
    · exact hX.sub hY
    · convert hx
      exact h_preimage_eq.symm
    · exact hX.sub hY
    congr
  rw [Kernel.entropy_congr h_ker, h_meas, Kernel.entropy_prodMkLeft_unit]

end

omit [Countable S] in
/-- The conditional Ruzsa distance is unchanged if the sets of random variables are replaced with
copies. -/
lemma condRuzsaDist_of_copy {X : Ω → G} (hX : Measurable X) {Z : Ω → S} (hZ : Measurable Z)
    {Y : Ω' → G} (hY : Measurable Y) {W : Ω' → T} (hW : Measurable W)
    {X' : Ω'' → G} (hX' : Measurable X') {Z' : Ω'' → S} (hZ' : Measurable Z')
    {Y' : Ω''' → G} (hY' : Measurable Y') {W' : Ω''' → T} (hW' : Measurable W')
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure μ''] [IsFiniteMeasure μ''']
    (h1 : IdentDistrib (⟨X, Z⟩) (⟨X', Z'⟩) μ μ'') (h2 : IdentDistrib (⟨Y, W⟩) (⟨Y', W'⟩) μ' μ''')
    [FiniteRange Z] [FiniteRange W] [FiniteRange Z'] [FiniteRange W'] :
    d[X | Z ; μ # Y | W ; μ'] = d[X' | Z' ; μ'' # Y' | W' ; μ'''] := by
  classical
  set A := (FiniteRange.toFinset Z) ∪ (FiniteRange.toFinset Z')
  set B := (FiniteRange.toFinset W) ∪ (FiniteRange.toFinset W')
  have hfull : Measure.prod (μ.map Z) (μ'.map W) ((A ×ˢ B : Finset (S × T)): Set (S × T))ᶜ = 0 := by
    simp only [A, B]
    apply Measure.prod_of_full_measure_finset
    all_goals {
      rw [Measure.map_apply ‹_›]
      convert measure_empty (μ := μ)
      simp [← FiniteRange.range]
      measurability
    }
  have hfull' : Measure.prod (μ''.map Z') (μ'''.map W')
    ((A ×ˢ B : Finset (S × T)): Set (S × T))ᶜ = 0 := by
    simp only [A, B]
    apply Measure.prod_of_full_measure_finset
    all_goals {
      rw [Measure.map_apply ‹_›]
      convert measure_empty (μ := μ)
      simp [← FiniteRange.range]
      measurability
    }
  rw [condRuzsaDist_def, condRuzsaDist_def, Kernel.rdist, Kernel.rdist,
    integral_eq_setIntegral hfull, integral_eq_setIntegral hfull', integral_finset _ _ .finset,
    integral_finset _ _ .finset]
  have hZZ' : μ.map Z = μ''.map Z' := (h1.comp measurable_snd).map_eq
  have hWW' : μ'.map W = μ'''.map W' := (h2.comp measurable_snd).map_eq
  simp_rw [Measure.prod_real_apply_singleton, ← hZZ', ← hWW',
    map_measureReal_apply hZ (.singleton _), map_measureReal_apply hW (.singleton _)]
  congr with x
  by_cases hz : μ (Z ⁻¹' {x.1}) = 0
  · simp only [smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero]
    refine .inr <| .inl ?_
    simp [Measure.real, hz]
  by_cases hw : μ' (W ⁻¹' {x.2}) = 0
  · simp only [smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero]
    refine .inr <| .inr ?_
    simp [Measure.real, hw]
  congr 2
  · have hZZ'x : μ (Z ⁻¹' {x.1}) = μ'' (Z' ⁻¹' {x.1}) := by
      have : μ.map Z {x.1} = μ''.map Z' {x.1} := by rw [hZZ']
      rwa [Measure.map_apply hZ (.singleton _),
        Measure.map_apply hZ' (.singleton _)] at this
    ext s hs
    rw [condDistrib_apply' hX hZ _ _ hz hs, condDistrib_apply' hX' hZ' _ _ _ hs]
    swap; · rwa [hZZ'x] at hz
    congr
    have : μ.map (⟨X, Z⟩) (s ×ˢ {x.1}) = μ''.map (⟨X', Z'⟩) (s ×ˢ {x.1}) := by rw [h1.map_eq]
    rwa [Measure.map_apply (hX.prodMk hZ) (hs.prod (.singleton _)),
      Measure.map_apply (hX'.prodMk hZ') (hs.prod (.singleton _)),
      Set.mk_preimage_prod, Set.mk_preimage_prod, Set.inter_comm,
      Set.inter_comm ((fun a ↦ X' a) ⁻¹' s)] at this
  · have hWW'x : μ' (W ⁻¹' {x.2}) = μ''' (W' ⁻¹' {x.2}) := by
      have : μ'.map W {x.2} = μ'''.map W' {x.2} := by rw [hWW']
      rwa [Measure.map_apply hW (.singleton _),
        Measure.map_apply hW' (.singleton _)] at this
    ext s hs
    rw [condDistrib_apply' hY hW _ _ hw hs, condDistrib_apply' hY' hW' _ _ _ hs]
    swap; · rwa [hWW'x] at hw
    congr
    have : μ'.map (⟨Y, W⟩) (s ×ˢ {x.2}) = μ'''.map (⟨Y', W'⟩) (s ×ˢ {x.2}) := by rw [h2.map_eq]
    rwa [Measure.map_apply (hY.prodMk hW) (hs.prod (.singleton _)),
      Measure.map_apply (hY'.prodMk hW') (hs.prod (.singleton _)),
      Set.mk_preimage_prod, Set.mk_preimage_prod, Set.inter_comm,
      Set.inter_comm ((fun a ↦ Y' a) ⁻¹' s)] at this

lemma condRuzsaDist'_of_copy (X : Ω → G) {Y : Ω' → G} (hY : Measurable Y)
    {W : Ω' → T} (hW : Measurable W)
    (X' : Ω'' → G) {Y' : Ω''' → G} (hY' : Measurable Y') {W' : Ω''' → T} (hW' : Measurable W')
    [IsFiniteMeasure μ'] [IsFiniteMeasure μ''']
    (h1 : IdentDistrib X X' μ μ'') (h2 : IdentDistrib (⟨Y, W⟩) (⟨Y', W'⟩) μ' μ''')
    [FiniteRange W] [FiniteRange W'] :
    d[X ; μ # Y | W ; μ'] = d[X' ; μ'' # Y' | W' ; μ'''] := by
  classical
  set A := (FiniteRange.toFinset W) ∪ (FiniteRange.toFinset W')
  have hfull : Measure.prod (dirac ()) (μ'.map W)
      ((Finset.univ (α := Unit) ×ˢ A : Finset (Unit × T)) : Set (Unit × T))ᶜ = 0 := by
    apply Measure.prod_of_full_measure_finset
    · simp
    simp only [A]
    rw [Measure.map_apply ‹_› (by measurability)]
    convert measure_empty (μ := μ)
    simp [← FiniteRange.range]
  have hfull' : Measure.prod (dirac ()) (μ'''.map W')
      ((Finset.univ (α := Unit) ×ˢ A : Finset (Unit × T)) : Set (Unit × T))ᶜ = 0 := by
    apply Measure.prod_of_full_measure_finset
    · simp
    simp only [A]
    rw [Measure.map_apply ‹_› (by measurability)]
    convert measure_empty (μ := μ)
    simp [← FiniteRange.range]
  rw [condRuzsaDist'_def, condRuzsaDist'_def, Kernel.rdist, Kernel.rdist,
    integral_eq_setIntegral hfull, integral_eq_setIntegral hfull', integral_finset _ _ .finset,
    integral_finset _ _ .finset]
  have hWW' : μ'.map W = μ'''.map W' := (h2.comp measurable_snd).map_eq
  simp_rw [Measure.prod_real_apply_singleton, ← hWW', map_measureReal_apply hW (.singleton _)]
  congr with x
  by_cases hw : μ' (W ⁻¹' {x.2}) = 0
  · simp only [smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero]
    refine .inr <| .inr ?_
    simp [Measure.real, hw]
  congr 2
  · rw [Kernel.const_apply, Kernel.const_apply, h1.map_eq]
  · have hWW'x : μ' (W ⁻¹' {x.2}) = μ''' (W' ⁻¹' {x.2}) := by
      have : μ'.map W {x.2} = μ'''.map W' {x.2} := by rw [hWW']
      rwa [Measure.map_apply hW (.singleton _),
        Measure.map_apply hW' (.singleton _)] at this
    ext s hs
    rw [condDistrib_apply' hY hW _ _ hw hs, condDistrib_apply' hY' hW' _ _ _ hs]
    swap; · rwa [hWW'x] at hw
    congr
    have : μ'.map (⟨Y, W⟩) (s ×ˢ {x.2}) = μ'''.map (⟨Y', W'⟩) (s ×ˢ {x.2}) := by rw [h2.map_eq]
    rwa [Measure.map_apply (hY.prodMk hW) (hs.prod (.singleton _)),
      Measure.map_apply (hY'.prodMk hW') (hs.prod (.singleton _)),
      Set.mk_preimage_prod, Set.mk_preimage_prod, Set.inter_comm,
      Set.inter_comm ((fun a ↦ Y' a) ⁻¹' s)] at this

lemma condRuszaDist_prod_eq_of_indepFun {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → G} {Y : Ω' → G}
    {W W' : Ω' → T} (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    (hW' : Measurable W') (h : IndepFun (⟨Y, W⟩) W' μ')
    [IsProbabilityMeasure μ'] [Finite T] :
    d[X ; μ # Y | ⟨W, W'⟩ ; μ'] = d[X ; μ # Y | W ; μ'] := by
  cases nonempty_fintype T
  rw [condRuzsaDist'_prod_eq_sum' _ _ hY hW hW']
  have : d[X ; μ # Y | W ; μ'] = ∑ z, μ'.real (W' ⁻¹' {z}) * d[X ; μ # Y | W ; μ'] := by
    rw [← Finset.sum_mul, sum_measureReal_preimage_singleton _ fun _ _ ↦ hW' <| .singleton _]
    simp
  rw [this]
  congr with w
  obtain hw | hw := eq_or_ne (μ'.real (W' ⁻¹' {w})) 0
  · simp [hw]
  congr 1
  apply condRuzsaDist'_of_copy _ hY hW _ hY hW (IdentDistrib.refl hX.aemeasurable)
    (h.identDistrib_cond (MeasurableSet.singleton w) (hY.prodMk hW) hW' ?_).symm
  intro h
  simp [measureReal_def, h] at hw

variable (μ μ') in
lemma condRuzsaDist_comp_right {T' : Type*} [Finite T] [Finite T'] [MeasurableSpace T']
    [MeasurableSingletonClass T'] [IsFiniteMeasure μ']
    (X : Ω → G) (Y : Ω' → G) (W : Ω' → T) (e : T → T')
    (hY : Measurable Y) (hW : Measurable W) (he : Measurable e)
    (h'e : Injective e) :
    d[X ; μ # Y | e ∘ W ; μ'] = d[X ; μ # Y | W ; μ'] := by
  cases nonempty_fintype T
  cases nonempty_fintype T'
  rw [condRuzsaDist'_eq_sum' hY (he.comp hW), condRuzsaDist'_eq_sum' hY hW]
  have A i : e ⁻¹' {e i} = {i} := by ext x; simp [h'e.eq_iff]
  symm
  refine Fintype.sum_of_injective e h'e _ _ (fun i hi ↦ ?_) (by simp [Set.preimage_comp, A])
  suffices e ⁻¹' {i} = ∅ by simp [Set.preimage_comp, this]
  simpa [Set.eq_empty_iff_forall_notMem] using hi

lemma condRuzsaDist_of_inj_map {G' : Type*} [Countable G'] [AddCommGroup G']
  [MeasurableSpace G'] [MeasurableSingletonClass G'] [IsProbabilityMeasure μ]
  (Y : Fin 4 → Ω → G) (h_indep : IndepFun (⟨Y 0, Y 2⟩) (⟨Y 1, Y 3⟩) μ)
  (h_meas : ∀ i, Measurable (Y i)) (π : G × G →+ G')
  (hπ : ∀ (h : G), Injective (fun g ↦ π (g, h)))
  [FiniteRange (Y 2)] [FiniteRange (Y 3)] :
    d[π ∘ ⟨Y 0, Y 2⟩ | Y 2 ; μ # π ∘ ⟨Y 1, Y 3⟩ | Y 3 ; μ] = d[Y 0 | Y 2 ; μ # Y 1 | Y 3 ; μ] := by
  let f (h : G) (g : G) : G' := π (g, h)
  let f' : G × G → G → G' := fun (h1, h2) ↦ fun g ↦ π (g, h1 - h2)
  have hf' (t : G × G) : Injective (f' t) := fun _ _ h ↦ hπ _ h
  let f'' : G × G → G' × G := fun (g, h) ↦ (π (g, h), h)
  have hf'' : Measurable f'' := .of_discrete
  have hm1 : Measurable (Y 0 - Y 1) := (h_meas 0).sub (h_meas 1)
  have hm2 : Measurable (⟨Y 2, Y 3⟩) := (h_meas 2).prodMk (h_meas 3)
  rw [condRuzsaDist_of_indep (h_meas 0) (h_meas 2) (h_meas 1) (h_meas 3) μ h_indep,
    condRuzsaDist_of_indep (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) μ
    (by exact h_indep.comp hf'' hf''),
    ← condEntropy_of_injective μ hm1 hm2 f' hf', ← map_comp_sub π,
    ← condEntropy_of_injective μ (h_meas 0) (h_meas 2) f hπ,
    ← condEntropy_of_injective μ (h_meas 1) (h_meas 3) f hπ]
  rfl

set_option linter.flexible false in
lemma condRuzsaDist'_of_inj_map [IsProbabilityMeasure μ] [Module (ZMod 2) G]
  {X B C : Ω → G}
    (hX : Measurable X) (hB : Measurable B) (hC : Measurable C)
    (h_indep : IndepFun X (⟨B, C⟩) μ) [FiniteRange X] [FiniteRange B] [FiniteRange C] :
    d[X ; μ # B | B + C ; μ] = d[X ; μ # C | B + C ; μ] := by
  let π : G × G →+ G :=
  { toFun := fun x ↦ x.2 - x.1
    map_zero' := by simp
    map_add' := fun a b ↦ by simp only [Prod.snd_add, Prod.fst_add, ZModModule.sub_eq_add]; abel }
  let Y : Fin 4 → Ω → G := ![-X, C, fun _ ↦ 0, B + C]
  have _ : FiniteRange (Y 0) := by simp [Y]; infer_instance
  have _ : FiniteRange (Y 1) := by simp [Y]; infer_instance
  have _ : FiniteRange (Y 2) := by simp [Y]; infer_instance
  have _ : FiniteRange (Y 3) := by simp [Y]; infer_instance
  have hY_meas i : Measurable (Y i) := by
    fin_cases i; exacts [hX.neg, hC, measurable_const, hB.add hC]
  calc d[X ; μ # B | B + C ; μ]
    = d[X | fun _ : Ω ↦ (0 : G) ; μ # B | B + C ; μ] := by rw [condRuzsaDist_of_const hX]
  _ = d[π ∘ ⟨-X, fun _ : Ω ↦ (0 : G)⟩ | fun _ : Ω ↦ (0 : G) ; μ # π ∘ ⟨C, B + C⟩ | B + C ; μ] := by
    congr
    · ext1 ω; simp [π]
    · ext1 ω
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, comp_apply, Pi.add_apply, π]
      abel
  _ = d[π ∘ ⟨Y 0, Y 2⟩ | Y 2 ; μ # π ∘ ⟨Y 1, Y 3⟩ | Y 3 ; μ] := by congr
  _ = d[-X | fun _ : Ω ↦ (0 : G) ; μ # C | B + C ; μ] := by
    rw [condRuzsaDist_of_inj_map _ _ hY_meas π (fun _ ↦ sub_right_injective)]
    · congr
    · have h1 : (⟨Y 0, Y 2⟩) = (fun x ↦ (-x, 0)) ∘ X := by ext1 ω; simp [Y]
      have h2 : (⟨Y 1, Y 3⟩) = (fun p ↦ (p.2, p.1 + p.2)) ∘ (⟨B, C⟩) := by
        ext ω : 1; simp [ZModModule.neg_eq_self, Y]
      rw [h1, h2]
      refine h_indep.comp ?_ ?_
      · exact measurable_neg.prodMk measurable_const
      · exact measurable_snd.prodMk (measurable_fst.add measurable_snd)
  _ = d[-X ; μ # C | B + C ; μ] := by rw [condRuzsaDist_of_const]; exact hX.neg
  _ = d[X ; μ # C | B + C ; μ] := by simp_rw [ZModModule.neg_eq_self]

lemma condRuzsaDist'_of_inj_map' [Module (ZMod 2) G] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ''] {A : Ω'' → G} {B C : Ω → G} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) [FiniteRange A] [FiniteRange B] [FiniteRange C] :
    d[A ; μ'' # B | B + C ; μ] = d[A ; μ'' # C | B + C ; μ] := by
  -- we want to apply `condRuzsaDist'_of_inj_map'`, but for that all variables need to
  -- be in the same probability space
  let Ω' := Ω'' × Ω
  set X₂' : Ω' → G := A ∘ Prod.fst with hX₂'_def
  have hX₂' : Measurable X₂' := hA.comp measurable_fst
  let B' : Ω' → G := B ∘ Prod.snd
  have hB' : Measurable B' := hB.comp measurable_snd
  let C' : Ω' → G := C ∘ Prod.snd
  have hC' : Measurable C' := hC.comp measurable_snd
  let μ' : Measure Ω' := Measure.prod μ'' μ
  have : IsProbabilityMeasure μ' := by infer_instance
  -- h1 and h2 should be applications of a new lemma?
  have h1 : d[A ; μ'' # B | B + C ; μ] = d[X₂' ; μ' # B' | B' + C' ; μ'] := by
    refine condRuzsaDist'_of_copy A hB (by fun_prop) X₂' hB' (by fun_prop) ?_ ?_
    · constructor
      · exact hA.aemeasurable
      · exact hX₂'.aemeasurable
      · rw [← Measure.map_map hA measurable_fst]
        simp [μ']
    · constructor
      · exact (hB.prodMk (hB.add hC)).aemeasurable
      · exact (hB'.prodMk (hB'.add hC')).aemeasurable
      · have : ⟨B', B' + C'⟩ = (⟨B, B + C⟩) ∘ Prod.snd := by ext1 _; simp [C', B']
        rw [this, ← Measure.map_map _ measurable_snd]
        · simp only [Measure.map_snd_prod, measure_univ, one_smul, μ']
        · exact hB.prodMk (hB.add hC)
  have h2 : d[A ; μ'' # C | B + C ; μ] = d[X₂' ; μ' # C' | B' + C' ; μ'] := by
    apply condRuzsaDist'_of_copy _ hC (by fun_prop) X₂' hC' (by fun_prop) ?_ ?_
    · constructor
      · exact hA.aemeasurable
      · exact hX₂'.aemeasurable
      · rw [← Measure.map_map hA measurable_fst]
        simp [μ']
    · constructor
      · exact (hC.prodMk (hB.add hC)).aemeasurable
      · exact (hC'.prodMk (hB'.add hC')).aemeasurable
      · have : ⟨C', B' + C'⟩ = (⟨C, B + C⟩) ∘ Prod.snd := by ext1 _; simp [B', C']
        rw [this, ← Measure.map_map _ measurable_snd]
        · simp only [Measure.map_snd_prod, measure_univ, one_smul, μ']
        · exact hC.prodMk (hB.add hC)
  rw [h1, h2, condRuzsaDist'_of_inj_map hX₂' hB' hC']
  rw [indepFun_iff_map_prod_eq_prod_map_map hX₂'.aemeasurable (hB'.prodMk hC').aemeasurable]
  have h_prod : (fun ω ↦ (X₂' ω, prod B' C' ω)) = Prod.map A (⟨B, C⟩) := by
    ext1
    simp only [comp_apply, X₂', B', C']
    rfl
  have h_comp_snd : (fun a ↦ (B' a, C' a)) = (⟨B, C⟩) ∘ Prod.snd := by ext1; simp [B', C']
  rw [h_prod, h_comp_snd, hX₂'_def, ← Measure.map_map _ measurable_snd,
    ← Measure.map_map _ measurable_fst, Measure.map_prod_map]
  rotate_left
  · exact hA
  · exact hB.prodMk hC
  · exact hA
  · exact hB.prodMk hC
  simp [μ']

/-- The **Kaimanovich-Vershik inequality**. `H[X + Y + Z] - H[X + Y] ≤ H[Y + Z] - H[Y]`. -/
lemma kaimanovich_vershik {X Y Z : Ω → G} (h : iIndepFun ![X, Y, Z] μ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    H[X + Y + Z ; μ] - H[X + Y ; μ] ≤ H[Y + Z ; μ] - H[Y ; μ] := by
  have : IsProbabilityMeasure μ := h.isProbabilityMeasure
  suffices (H[X ; μ] + H[Y ; μ] + H[Z ; μ]) + H[X + Y + Z ; μ]
    ≤ (H[X ; μ] + H[Y + Z ; μ]) + (H[Z ; μ] + H[X + Y ; μ]) by linarith
  have : ∀ (i : Fin 3), Measurable (![X, Y, Z] i) := fun i ↦ by fin_cases i <;> assumption
  convert entropy_triple_add_entropy_le μ hX hZ (show Measurable (X + (Y + Z)) by fun_prop)
    using 2
  · calc
      H[X ; μ] + H[Y ; μ] + H[Z ; μ] = H[⟨X, Y⟩ ; μ] + H[Z ; μ] := by
        rw [IndepFun.entropy_pair_eq_add hX hY]
        convert h.indepFun (show 0 ≠ 1 by decide)
      _ = H[⟨⟨X, Y⟩, Z⟩ ; μ] := by
        rw [IndepFun.entropy_pair_eq_add (hX.prodMk hY) hZ]
        exact h.indepFun_prodMk this 0 1 2 (by decide) (by decide)
      _ = H[⟨X, ⟨Z , X + (Y + Z)⟩⟩ ; μ] := by
        apply entropy_of_comp_eq_of_comp μ (by fun_prop) (by fun_prop)
          (fun ((x, y), z) ↦ (x, z, x + y + z)) (fun (a, b, c) ↦ ((a, c - a - b), b))
        all_goals { funext ω; dsimp [prod]; ext <;> dsimp; abel }
  · rw [add_assoc]
  · symm
    refine (entropy_add_right hX (by fun_prop) _).trans <|
      IndepFun.entropy_pair_eq_add hX (by fun_prop) ?_
    exact h.indepFun_add_right this 0 1 2 (by decide) (by decide)
  · rw [eq_comm, ← add_assoc]
    refine (entropy_add_right' hZ (by fun_prop) _).trans <|
      IndepFun.entropy_pair_eq_add hZ (by fun_prop) ?_
    exact h.indepFun_add_right this 2 0 1 (by decide) (by decide)

/-- A version of the **Kaimanovich-Vershik inequality** with some variables negated. -/
lemma kaimanovich_vershik' {X Y Z : Ω → G} (h : iIndepFun ![X, Y, Z] μ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    H[X - (Y + Z) ; μ] - H[X - Y ; μ] ≤ H[Y + Z ; μ] - H[Y ; μ] := by
  rw [← entropy_neg (X := Y + Z) (by fun_prop), ← entropy_neg hY]
  simp_rw [sub_eq_add_neg, neg_add, ← add_assoc]
  refine kaimanovich_vershik ?_ hX hY.neg hZ.neg
  convert (h.neg 1).neg 2
  ext i; fin_cases i
  · simp (discharger := decide)
  · simp (discharger := decide)
  · rw [← show ∀ h : 2 < 3, (2 : Fin 3) = ⟨2, h⟩ by intro; rfl]
    simp (discharger := decide)

section BalogSzemerediGowers

/-- The **entropic Balog-Szemerédi-Gowers inequality**. Let `A, B` be `G`-valued random variables on
`Ω`, and set `Z := A+B`. Then
`∑ z, P[Z=z] d[(A | Z = z) ; (B | Z = z)] ≤ 3 I[A :B] + 2 H[Z] - H[A] - H[B].`
TODO: remove the hypothesis of `Fintype G` from here and from `condIndep_copies'` -/
lemma ent_bsg [IsProbabilityMeasure μ] {A B : Ω → G} (hA : Measurable A) (hB : Measurable B)
    [Finite G] :
    (μ.map (A + B))[fun z ↦ d[A ; μ[|(A + B) ⁻¹' {z}] # B ; μ[|(A + B) ⁻¹' {z}]]]
      ≤ 3 * I[A : B; μ] + 2 * H[A + B ; μ] - H[A ; μ] - H[B ; μ] := by
  let Z := A + B
  have hZ : Measurable Z := hA.add hB
  obtain ⟨Ω', _, AB₁, AB₂, Z', ν, _, hAB₁, hAB₂, hZ', hABZ, hABZ₁, hABZ₂, hZ₁, hZ₂⟩ :=
    condIndep_copies' (⟨A, B⟩) Z (hA.prodMk hB) hZ μ (fun (a, b) c ↦ c = a + b)
    .of_discrete (Eventually.of_forall fun _ ↦ rfl)
  let A₁ := fun ω ↦ (AB₁ ω).1
  let B₁ := fun ω ↦ (AB₁ ω).2
  let A₂ := fun ω ↦ (AB₂ ω).1
  let B₂ := fun ω ↦ (AB₂ ω).2
  replace hZ₁ : Z' = A₁ + B₁ := funext hZ₁
  replace hZ₂ : Z' = A₂ + B₂ := funext hZ₂
  have hA₁ : Measurable A₁ := hAB₁.fst
  have hB₁ : Measurable B₁ := hAB₁.snd
  have hA₂ : Measurable A₂ := hAB₂.fst
  have hB₂ : Measurable B₂ := hAB₂.snd
  have hZZ' : IdentDistrib Z' Z ν μ := hABZ₁.comp measurable_snd
  have :=
    calc
      H[⟨A₁, ⟨B₁, A₁ - B₂⟩⟩ ; ν]
        = H[⟨⟨A₁, B₁⟩, ⟨⟨A₂, B₂⟩, Z'⟩⟩ ; ν] := entropy_of_comp_eq_of_comp _
          (hA₁.prodMk <| hB₁.prodMk <| hA₁.sub hB₂) (hAB₁.prodMk <| hAB₂.prodMk hZ')
            (fun (a, b, c) ↦ ((a, b), (b + c, a - c), a + b))
            (fun ((a, b), (_c, d), _e) ↦ (a, b, a - d))
          (by funext; simpa [sub_add_eq_add_sub, Prod.ext_iff, ← hZ₁, hZ₂, two_nsmul,
            ← add_sub_assoc, add_comm, eq_sub_iff_add_eq]
             using congr_fun (hZ₂.symm.trans hZ₁) _) rfl
      _ = H[⟨⟨A₁, B₁⟩, Z'⟩ ; ν] + H[⟨⟨A₂, B₂⟩, Z'⟩ ; ν] - H[Z' ; ν] :=
        ent_of_cond_indep _ hAB₁ hAB₂ hZ' hABZ
      _ = 2 * H[⟨⟨A, B⟩, Z⟩ ; μ] - H[Z ; μ] := by
        rw [two_mul]
        congr 1
        congr 1 <;> exact IdentDistrib.entropy_congr ‹_›
        exact hZZ'.entropy_congr
      _ = 2 * H[⟨A, B⟩ ; μ] - H[Z ; μ] := by
        congr 2
        exact entropy_prod_comp (hA.prodMk hB) _ fun x ↦ x.1 + x.2
  have :=
    calc
      H[⟨A₁, A₁ - B₂⟩ ; ν]
        = H[⟨A₁, B₂⟩ ; ν] := entropy_sub_right hA₁ hB₂ _
      _ ≤ H[A₁ ; ν] + H[B₂ ; ν] := entropy_pair_le_add hA₁ hB₂ _
      _ = H[A ; μ] + H[B ; μ] := by
        congr 1
        · exact (hABZ₁.comp measurable_fst.fst).entropy_congr
        · exact (hABZ₂.comp measurable_fst.snd).entropy_congr
  have :=
    calc
      H[⟨B₁, A₁ - B₂⟩ ; ν]
        = H[⟨A₂, B₁⟩ ; ν] := by
          rw [entropy_comm hB₁ (show Measurable (A₁ - B₂) from hA₁.sub hB₂),
            ← entropy_sub_left' hA₂ hB₁, sub_eq_sub_iff_add_eq_add.2 <| hZ₁.symm.trans hZ₂]
      _ ≤ H[A₂ ; ν] + H[B₁ ; ν] := entropy_pair_le_add hA₂ hB₁ _
      _ = H[A ; μ] + H[B ; μ] := by
        congr 1
        · exact (hABZ₂.comp measurable_fst.fst).entropy_congr
        · exact (hABZ₁.comp measurable_fst.snd).entropy_congr
  have :=
    calc
     _ ≤ _ := entropy_triple_add_entropy_le ν hA₁ hB₁ (show Measurable (A₁ - B₂) from hA₁.sub hB₂)
     _ ≤ _ := add_le_add ‹_› ‹_›
  have :=
    calc
      H[A₁ - B₂ | Z' ; ν]
        ≤ H[A₁ - B₂ ; ν] := condEntropy_le_entropy _ (hA₁.sub hB₂) hZ'
      _ ≤ _ := le_sub_iff_add_le'.2 ‹_›
      _ = 2 * I[A : B ; μ] + H[Z ; μ] := by
        rw [‹H[⟨A₁, ⟨B₁, A₁ - B₂⟩⟩ ; ν] = _›, mutualInfo_def]; ring
  have hA₁Z :=
    calc
      H[A₁ | Z' ; ν]
      _ = H[⟨A₁, B₁⟩ ; ν] - H[Z' ; ν] := by
        rw [chain_rule'', hZ₁, entropy_add_right, entropy_comm] <;> assumption
      _ = H[⟨A, B⟩ ; μ] - H[Z ; μ] := by
        congr 1
        · exact (hABZ₁.comp measurable_fst).entropy_congr
        · exact hZZ'.entropy_congr
      _ = H[A ; μ] + H[B ; μ] - I[A : B ; μ] - H[Z ; μ] := by
        rw [← entropy_add_entropy_sub_mutualInfo]
  have hB₂Z :=
    calc
      H[B₂ | Z' ; ν]
      _ = H[⟨A₂, B₂⟩ ; ν] - H[Z' ; ν] := by
        rw [chain_rule'', hZ₂, entropy_add_right', entropy_comm] <;> assumption
      _ = H[⟨A, B⟩ ; μ] - H[Z ; μ] := by
        congr 1
        · exact (hABZ₂.comp measurable_fst).entropy_congr
        · exact hZZ'.entropy_congr
      _ = H[A ; μ] + H[B ; μ] - I[A : B ; μ] - H[Z ; μ] := by
        rw [← entropy_add_entropy_sub_mutualInfo]
  calc
    (μ.map Z)[fun z ↦ d[A ; μ[|Z ← z] # B ; μ[|Z ← z]]]
      = (ν.map Z')[fun z ↦ d[A₁ ; ν[|Z' ← z] # B₂ ; ν[|Z' ← z]]] := by
        rw [hZZ'.map_eq]
        refine integral_congr_ae <| Eventually.of_forall fun z ↦ ?_
        have hAA₁ : IdentDistrib A₁ A (ν[|Z' ← z]) (μ[|Z ← z]) :=
          (hABZ₁.comp <| measurable_fst.fst.prodMk measurable_snd).cond
            (.singleton z) hZ' hZ
        have hBB₂ : IdentDistrib B₂ B (ν[|Z' ← z]) (μ[|Z ← z]) :=
          (hABZ₂.comp <| measurable_fst.snd.prodMk measurable_snd).cond
            .of_discrete hZ' hZ
        dsimp (config := {zeta := false}) [rdist]
        rw [← hAA₁.entropy_congr, ← hBB₂.entropy_congr, hAA₁.map_eq, hBB₂.map_eq]
    _ = (ν.map Z')[fun z ↦
          H[A₁ - B₂ ; ν[|Z' ← z]] - H[A₁ ; ν[|Z' ← z]]/2 - H[B₂ ; ν[|Z' ← z]]/2] := by
        apply integral_congr_ae
        apply hABZ.mono
        intro z hz
        exact (hz.comp measurable_fst measurable_snd).rdist_eq hA₁ hB₂
    _ = H[A₁ - B₂ | Z' ; ν] - H[A₁ | Z' ; ν] / 2 - H[B₂ | Z' ; ν] / 2 := by
        rw [integral_sub, integral_sub, integral_div, integral_div]
        · rfl
        all_goals exact .of_finite
    _ ≤ 2 * I[A : B ; μ] + H[Z ; μ] - H[A₁ | Z' ; ν] / 2 - H[B₂ | Z' ; ν] / 2 :=
        sub_le_sub_right (sub_le_sub_right ‹_› _) _
    _ = _ := by rw [hA₁Z, hB₂Z]; ring

end BalogSzemerediGowers

variable (μ μ') in
/-- Suppose that $(X, Z)$ and $(Y, W)$ are random variables, where $X, Y$ take values in an abelian
group. Then $$d[X | Z ; Y | W] \leq d[X ; Y] + \tfrac{1}{2} I[X : Z] + \tfrac{1}{2} I[Y : W]$$ -/
lemma condRuzsaDist_le [Countable T] {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] [FiniteRange W] :
      d[X | Z ; μ # Y|W ; μ'] ≤ d[X ; μ # Y ; μ'] + I[X : Z ; μ]/2 + I[Y : W ; μ']/2 := by
  have hXZ : Measurable (⟨X, Z⟩ : Ω → G × S):= hX.prodMk hZ
  have hYW : Measurable (⟨Y, W⟩ : Ω' → G × T):= hY.prodMk hW
  obtain ⟨ν, XZ', YW', _, hXZ', hYW', hind, hIdXZ, hIdYW, _, _⟩ :=
    independent_copies_finiteRange hXZ hYW μ μ'
  let X' := Prod.fst ∘ XZ'
  let Z' := Prod.snd ∘ XZ'
  let Y' := Prod.fst ∘ YW'
  let W' := Prod.snd ∘ YW'
  have hX' : Measurable X' := hXZ'.fst
  have hZ' : Measurable Z' := hXZ'.snd
  have hY' : Measurable Y' := hYW'.fst
  have hW' : Measurable W' := hYW'.snd
  have : FiniteRange W' := instFiniteRangeComp ..
  have : FiniteRange X' := instFiniteRangeComp ..
  have : FiniteRange Y' := instFiniteRangeComp ..
  have : FiniteRange Z' := instFiniteRangeComp ..
  have hind' : IndepFun X' Y' ν := hind.comp measurable_fst measurable_fst
  rw [show XZ' = ⟨X', Z'⟩ by rfl] at hIdXZ hind
  rw [show YW' = ⟨Y', W'⟩ by rfl] at hIdYW hind
  rw [← condRuzsaDist_of_copy hX' hZ' hY' hW' hX hZ hY hW hIdXZ hIdYW,
    condRuzsaDist_of_indep hX' hZ' hY' hW' _ hind]
  have hIdX : IdentDistrib X X' μ ν := hIdXZ.symm.comp measurable_fst
  have hIdY : IdentDistrib Y Y' μ' ν := hIdYW.symm.comp measurable_fst
  rw [hIdX.rdist_congr hIdY, hIdXZ.symm.mutualInfo_eq, hIdYW.symm.mutualInfo_eq,
    hind'.rdist_eq hX' hY', mutualInfo_eq_entropy_sub_condEntropy hX' hZ',
    mutualInfo_eq_entropy_sub_condEntropy hY' hW']
  have h := condEntropy_le_entropy ν (X := X' - Y') (hX'.sub hY') (hZ'.prodMk hW')
  linarith [h, entropy_nonneg Z' ν, entropy_nonneg W' ν]

variable (μ μ') in
lemma condRuzsaDist_le' [Countable T] {X : Ω → G} {Y : Ω' → G} {W : Ω' → T}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    [FiniteRange X] [FiniteRange Y] [FiniteRange W] :
    d[X ; μ # Y|W ; μ'] ≤ d[X ; μ # Y ; μ'] + I[Y : W ; μ']/2 := by
  rw [← condRuzsaDist_of_const hX _ _ (0 : Fin 1)]
  refine (condRuzsaDist_le μ μ' hX measurable_const hY hW).trans ?_
  simp [mutualInfo_const hX (0 : Fin 1)]

variable (μ μ') in
lemma condRuzsaDist_le'_prod [Countable T] {X : Ω → G} {Y : Ω' → G} {W Z : Ω' → T}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange W] [FiniteRange Z] :
    d[X ; μ # Y|⟨W, Z⟩ ; μ'] ≤ d[X ; μ # Y|Z ; μ'] + I[Y : W | Z ; μ']/2 := by
  rw [condRuzsaDist'_prod_eq_sum _ _ hY hW hZ, condRuzsaDist'_eq_sum hY hZ,
    condMutualInfo_eq_sum hZ, Finset.sum_div, ← Finset.sum_add_distrib]
  gcongr with z
  rw [mul_div_assoc, ← mul_add]
  rcases eq_or_ne (μ' (Z ⁻¹' {z})) 0 with hz | hz
  · simp [measureReal_def, hz]
  · have : IsProbabilityMeasure (μ'[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure hz
    gcongr
    exact condRuzsaDist_le' _ _ hX hY hW

variable (μ) in
lemma comparison_of_ruzsa_distances [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    d[X ; μ # Y+ Z ; μ'] - d[X ; μ # Y ; μ'] ≤ (H[Y + Z; μ'] - H[Y; μ']) / 2 ∧
    (Module (ZMod 2) G →
      H[Y + Z; μ'] - H[Y; μ'] = d[Y; μ' # Z; μ'] + H[Z; μ'] / 2 - H[Y; μ'] / 2) := by
  obtain ⟨Ω'', mΩ'', μ'', X', Y', Z', hμ, hi, hX', hY', hZ', h2X', h2Y', h2Z', _, _, _⟩ :=
    independent_copies3_nondep_finiteRange hX hY hZ μ μ' μ'
  have hY'Z' : IndepFun Y' Z' μ'' := hi.indepFun (show (1 : Fin 3) ≠ 2 by decide)
  have h2 : IdentDistrib (Y' + Z') (Y + Z) μ'' μ' := h2Y'.add h2Z' hY'Z' h
  have hm : ∀ (i : Fin 3), Measurable (![X', Y', Z'] i) :=
    fun i ↦ by fin_cases i <;> (dsimp; assumption)
  have hXY' : IndepFun X' Y' μ'' := hi.indepFun (show (0 : Fin 3) ≠ 1 by decide)
  have hYZ' : IndepFun Y' Z' μ'' := hi.indepFun (show (1 : Fin 3) ≠ 2 by decide)
  have hXYZ' : IndepFun X' (Y' + Z') μ'' := by
    symm
    exact hi.indepFun_add_left hm 1 2 0 (by decide) (by decide)
  rw [← h2X'.rdist_congr h2Y', ← h2X'.rdist_congr h2, ← h2Y'.rdist_congr h2Z',
    ← h2.entropy_congr, ← h2Y'.entropy_congr, ← h2Z'.entropy_congr]
  rw [hXY'.rdist_eq hX' hY', hYZ'.rdist_eq hY' hZ', hXYZ'.rdist_eq hX' (hY'.add hZ')]
  constructor
  · linarith [kaimanovich_vershik' hi hX' hY' hZ']
  · intro hG
    rw [ZModModule.sub_eq_add Y' Z']
    ring

variable (μ) in
/-- Let `X, Y, Z` be random variables taking values in some abelian group, and with `Y, Z`
independent. Then we have
`d[X ; Y + Z] - d[X ; Y] ≤ 1/2 (H[Y+ Z] - H[Y])`
$$= \tfrac{1}{2} d[Y ; Z] + \tfrac{1}{4} H[Z] - \tfrac{1}{4} H[Y]$$
and
$$d[X ; Y|Y+ Z] - d[X ; Y] \leq \tfrac{1}{2} \bigl(H[Y+ Z] - H[Z]\bigr)$$
$$= \tfrac{1}{2} d[Y ; Z] + \tfrac{1}{4} H[Y] - \tfrac{1}{4} H[Z]$$
-/
lemma condRuzsaDist_diff_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    d[X ; μ # Y+ Z ; μ'] - d[X ; μ # Y ; μ'] ≤ (H[Y + Z; μ'] - H[Y; μ']) / 2 :=
  (comparison_of_ruzsa_distances μ hX hY hZ h).1

variable (μ) [Module (ZMod 2) G] in
lemma entropy_sub_entropy_eq_condRuzsaDist_add [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    H[Y + Z; μ'] - H[Y; μ'] = d[Y; μ' # Z; μ'] + H[Z; μ'] / 2 - H[Y; μ'] / 2 :=
  (comparison_of_ruzsa_distances μ hX hY hZ h).2 ‹_›

variable (μ) [Module (ZMod 2) G] in
lemma condRuzsaDist_diff_le' [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    d[X ; μ # Y + Z; μ'] - d[X ; μ # Y; μ'] ≤
    d[Y; μ' # Z; μ'] / 2 + H[Z; μ'] / 4 - H[Y; μ'] / 4 := by
  linarith [condRuzsaDist_diff_le μ hX hY hZ h,
    entropy_sub_entropy_eq_condRuzsaDist_add μ hX hY hZ h]

variable (μ) in
lemma condRuzsaDist_diff_le'' [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    d[X ; μ # Y|Y+ Z ; μ'] - d[X ; μ # Y ; μ'] ≤ (H[Y+ Z ; μ'] - H[Z ; μ'])/2 := by
  rw [← mutualInfo_add_right hY hZ h]
  linarith [condRuzsaDist_le' (W := Y + Z) μ μ' hX hY (by fun_prop)]

variable (μ) [Module (ZMod 2) G] in
lemma condRuzsaDist_diff_le''' [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] :
    d[X ; μ # Y|Y+ Z ; μ'] - d[X ; μ # Y ; μ'] ≤
    d[Y ; μ' # Z ; μ']/2 + H[Y ; μ']/4 - H[Z ; μ']/4 := by
  linarith [condRuzsaDist_diff_le'' μ hX hY hZ h,
    entropy_sub_entropy_eq_condRuzsaDist_add μ hX hY hZ h]

variable (μ) in
lemma condRuzsaDist_diff_ofsum_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y Z Z' : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hZ' : Measurable Z')
    (h : iIndepFun ![Y, Z, Z'] μ')
    [FiniteRange X] [FiniteRange Z] [FiniteRange Y] [FiniteRange Z'] :
    d[X ; μ # Y + Z | Y + Z + Z'; μ'] - d[X ; μ # Y; μ'] ≤
    (H[Y + Z + Z'; μ'] + H[Y + Z; μ'] - H[Y ; μ'] - H[Z' ; μ'])/2 := by
  have hadd : IndepFun (Y + Z) Z' μ' :=
    (h.indepFun_add_left (Fin.cases hY <| Fin.cases hZ <| Fin.cases hZ' Fin.rec0) 0 1 2
      (show 0 ≠ 2 by decide) (show 1 ≠ 2 by decide))
  have h1 := condRuzsaDist_diff_le'' μ hX (show Measurable (Y + Z) by fun_prop) hZ' hadd
  have h2 := condRuzsaDist_diff_le μ hX hY hZ (h.indepFun (show 0 ≠ 1 by decide))
  linarith [h1, h2]
