import Mathlib.Probability.Notation
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import PFR.Entropy.KernelRuzsa
import PFR.Entropy.Basic
import PFR.ForMathlib.FiniteMeasureComponent
import PFR.f2_vec
import PFR.ProbabilityMeasureProdCont


/-!
# Ruzsa distance

Here we define Ruzsa distance and establish its basic properties.

## Main definitions

* `rdist` : The Ruzsa distance $d[X; Y]$ between two random variables
* `cond_rdist` : The conditional Ruzsa distance $d[X|Z; Y|W]$ (or $d[X; Y|W]$) between two random variables, conditioned on additional random variables

## Main results

* `rdist_triangle` : The Ruzsa triangle inequality for three random variables.

-/
open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} {Ω' Ω'' Ω''' G T : Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Fintype G]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]

variable {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}

-- may also want [DecidableEq G]

/-- If $X$ is $G$-valued, then $H[-X]=H[X]$. -/
lemma entropy_neg (hX : Measurable X) : H[-X ; μ] = H[X ; μ] :=
  entropy_comp_of_injective μ hX (fun x ↦ - x) neg_injective

/-- $$H[X-Y]=H[Y-X].$$ -/
lemma entropy_sub_comm {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) :
    H[X - Y ; μ] = H[Y - X ; μ] := by
  rw [← neg_sub]
  exact entropy_neg (hY.sub hX)

lemma condEntropy_of_sum_eq {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] : H[X+Y | Y ; μ] = H[X | Y ; μ] := by
  refine condEntropy_of_inj_map μ hX hY (fun y x ↦ x + y) ?_
  exact fun y ↦ add_left_injective y

/-- $$H[X] - I[X :Y] \leq H[X+Y].$$ -/
lemma entropy_sub_mutualInformation_le_entropy_add
    {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] :
    H[X ; μ] - I[X : Y ; μ] ≤ H[X + Y ; μ] := by
  rw [mutualInformation_eq_entropy_sub_condEntropy hX hY]
  ring_nf
  rw [<- condEntropy_of_sum_eq hX hY]
  exact condEntropy_le_entropy _ (hX.add hY) hY

lemma condEntropy_of_sub_eq {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] : H[X-Y | Y ; μ] = H[X | Y ; μ] := by
  refine condEntropy_of_inj_map μ hX hY (fun y x ↦ x - y) ?_
  exact fun y ↦ sub_left_injective

/-- $$H[X] - I[X :Y] \leq H[X-Y].$$ -/
lemma entropy_sub_mutualInformation_le_entropy_sub
    {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] :
    H[X ; μ] - I[X : Y ; μ] ≤ H[X - Y ; μ] := by
  rw [mutualInformation_eq_entropy_sub_condEntropy hX hY]
  ring_nf
  rw [<- condEntropy_of_sub_eq hX hY]
  exact condEntropy_le_entropy _ (hX.sub hY) hY

/--$$H[X, X+Y] = H[X, Y]$$ --/
lemma entropy_of_shear_eq {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] : H[⟨ X, X+Y⟩ ; μ] = H[⟨ X, Y⟩ ; μ] := by
  rw [chain_rule' μ hX hY, chain_rule' μ hX _]
  . congr 1
    rw [add_comm]
    exact condEntropy_of_sum_eq hY hX
  exact Measurable.add' hX hY

/--$$H[X, Y-X] = H[X, Y]$$ --/
lemma entropy_of_shear_eq' {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] : H[⟨ X, Y-X⟩ ; μ] = H[⟨ X, Y⟩ ; μ] := by
  rw [chain_rule' μ hX hY, chain_rule' μ hX _]
  . congr 1
    exact condEntropy_of_sub_eq hY hX
  exact Measurable.sub' hY hX

/-- $$ \max(H[X], H[Y]) - I[X :Y] \leq H[X + Y].$$ -/
lemma ent_of_sum_lower {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y)
    [IsProbabilityMeasure μ] :
    (max H[X ; μ] H[Y ; μ]) - I[X : Y ; μ] ≤ H[X + Y ; μ] := by
  rw [sub_le_iff_le_add']
  refine max_le ?_ ?_
  · rw [← sub_le_iff_le_add']
    exact entropy_sub_mutualInformation_le_entropy_add hX hY
  · rw [← sub_le_iff_le_add', mutualInformation_comm hX hY, add_comm X]
    exact entropy_sub_mutualInformation_le_entropy_add hY hX

/-- $$ \max(H[X], H[Y]) - I[X :Y] \leq H[X - Y].$$ -/
lemma ent_of_diff_lower {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y)
    [IsProbabilityMeasure μ] :
  (max H[X ; μ] H[Y ; μ]) - I[X : Y ; μ] ≤ H[X - Y ; μ] := by
  rw [sub_le_iff_le_add']
  refine max_le ?_ ?_
  · rw [← sub_le_iff_le_add']
    exact entropy_sub_mutualInformation_le_entropy_sub hX hY
  · rw [← sub_le_iff_le_add', mutualInformation_comm hX hY, entropy_sub_comm hX hY]
    exact entropy_sub_mutualInformation_le_entropy_sub hY hX

/-- $$ \max(H[X|Z], H[Y|Z]) - I[X :Y|Z] \leq H[X + Y|Z] $$ -/
lemma condEnt_of_sum_lower {Y : Ω → G} {Z : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsProbabilityMeasure μ] :
    (max H[X | Z ; μ] H[Y | Z ; μ]) - I[X : Y | Z ; μ] ≤ H[X + Y | Z ; μ] := by
  have : IsMarkovKernel (condEntropyKernel (fun a ↦ (Y a, X a)) Z μ) :=
    isMarkovKernel_condEntropyKernel (hY.prod_mk hX) hZ μ
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  rw [condMutualInformation_comm hX hY, condEntropy_eq_kernel_entropy hX hZ,
    condEntropy_eq_kernel_entropy hY hZ, condMutualInformation_eq_kernel_mutualInfo hY hX hZ,
    condEntropy_eq_kernel_entropy ?_ hZ]
  swap ; · exact hX.add hY
  rw [kernel.entropy_congr (condEntropyKernel_snd_ae_eq hY hX hZ μ).symm,
    kernel.entropy_congr (condEntropyKernel_fst_ae_eq hY hX hZ μ).symm,
    max_comm]
  refine (kernel.ent_of_sum_lower _ _ ).trans_eq ?_
  have h := condEntropyKernel_comp (hY.prod_mk hX) hZ μ (fun x ↦ x.1 + x.2)
  rw [kernel.entropy_congr h.symm]
  congr with ω
  simp [add_comm (X ω)]

/-- $$ \max(H[X|Z], H[Y|Z]) - I[X :Y|Z] \leq H[X - Y|Z] $$ -/
lemma condEnt_of_diff_lower {Y : Ω → G} {Z : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsProbabilityMeasure μ] :
    (max H[X | Z ; μ] H[Y | Z ; μ]) - I[X : Y | Z ; μ] ≤ H[X - Y | Z ; μ] := by
  have : IsMarkovKernel (condEntropyKernel (fun a ↦ (Y a, X a)) Z μ) :=
    isMarkovKernel_condEntropyKernel (hY.prod_mk hX) hZ μ
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  rw [condMutualInformation_comm hX hY, condEntropy_eq_kernel_entropy hX hZ,
    condEntropy_eq_kernel_entropy hY hZ, condMutualInformation_eq_kernel_mutualInfo hY hX hZ,
    condEntropy_eq_kernel_entropy ?_ hZ]
  swap ; · exact hX.sub hY
  rw [kernel.entropy_congr (condEntropyKernel_snd_ae_eq hY hX hZ μ).symm,
    kernel.entropy_congr (condEntropyKernel_fst_ae_eq hY hX hZ μ).symm,
    max_comm]
  refine (kernel.ent_of_diff_lower _ _ ).trans_eq ?_
  rw [kernel.entropy_sub_comm]
  have h := condEntropyKernel_comp (hY.prod_mk hX) hZ μ (fun x ↦ x.2 - x.1)
  rw [kernel.entropy_congr h.symm]
  rfl

/-- If $X, Y$ are independent, then $$ \max(H[X], H[Y]) \leq H[X + Y]$$. -/
lemma ent_of_indep_sum_lower  {X : Ω → G} {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y μ) [IsProbabilityMeasure μ] :
    max H[X ; μ] H[Y ; μ] ≤ H[X + Y ; μ] := by
  calc max H[X ; μ] H[Y ; μ] = (max H[X ; μ] H[Y ; μ]) - I[X : Y ; μ] := by
        rw [(mutualInformation_eq_zero hX hY).mpr h, sub_zero]
  _ ≤ H[X + Y ; μ] := ent_of_sum_lower hX hY

/-- If $X, Y$ are independent, then $$ \max(H[X], H[Y]) \leq H[X - Y]$$. -/
lemma ent_of_indep_diff_lower  {X : Ω → G} {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y μ) [IsProbabilityMeasure μ] :
    (max H[X ; μ] H[Y ; μ]) ≤ H[X - Y ; μ] := by
  have : IndepFun X (-Y) μ := h.comp measurable_id measurable_neg
  convert ent_of_indep_sum_lower hX hY.neg this using 2
  · exact (entropy_neg hY).symm
  · ext x ; simp [sub_eq_add_neg]

/-- The Ruzsa distance `dist X Y` between two random variables is defined as
$H[X'-Y'] - H[X']/2 - H[Y']/2$, where $X', Y'$ are independent copies of $X, Y$. -/
noncomputable
def rdist (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  H[fun x ↦ x.1 - x.2 ; (μ.map X).prod (μ'.map Y)] - H[X ; μ]/2 - H[Y ; μ']/2

/- Needed a new separator here, chose `#` arbitrarily, but am open to other suggestions -/
@[inherit_doc rdist] notation3:max "d[" X " ; " μ " # " Y " ; " μ' "]" => rdist X Y μ μ'

@[inherit_doc rdist] notation3:max "d[" X " # " Y "]" => rdist X Y volume volume

lemma rdist_def (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω) (μ' : Measure Ω') :
    d[ X ; μ # Y ; μ' ]
      = H[fun x ↦ x.1 - x.2 ; (μ.map X).prod (μ'.map Y)] - H[X ; μ]/2 - H[Y ; μ']/2 := rfl

-- TODO: Use notation `Hm[μ]` here? (figure out how)
lemma continuous_measureEntropy_probabilityMeasure {Ω : Type*} [Fintype Ω]
    [TopologicalSpace Ω] [DiscreteTopology Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] :
    Continuous (fun (μ : ProbabilityMeasure Ω) ↦ measureEntropy (S := Ω) μ) := by
  apply continuous_finset_sum
  intro ω _
  apply Real.continuous_negIdMulLog.comp
  simp only [measure_univ, inv_one, one_smul]
  exact continuous_probabilityMeasure_apply_of_isClopen (s := {ω}) ⟨isOpen_discrete _, T1Space.t1 _⟩

lemma continuous_entropy_restrict_probabilityMeasure
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] :
    Continuous (fun (μ : ProbabilityMeasure G) ↦ H[ id ; μ.toMeasure ]) := by
  simp only [entropy_def, Measure.map_id]
  exact continuous_measureEntropy_probabilityMeasure

lemma continuous_rdist_restrict_probabilityMeasure
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] :
    Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦
        d[ id ; μ.1.toMeasure # id ; μ.2.toMeasure ]) := by
  simp [rdist_def]
  have obs₀ : Continuous (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦
      H[fun x ↦ x.1 - x.2 ; μ.1.toMeasure.prod μ.2.toMeasure]) := by
    simp_rw [entropy_def]
    have diff_cts : Continuous (fun (x : G × G) ↦ x.1 - x.2) := by continuity
    have key₁ := ProbabilityMeasure.continuous_prod_of_fintype (α := G) (β := G)
    have key₂ := ProbabilityMeasure.continuous_map diff_cts
    convert (@continuous_measureEntropy_probabilityMeasure G _ _ _ _ _).comp (key₂.comp key₁)
  have obs₁ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ H[ id ; μ.1.toMeasure ]) := by
    convert (continuous_measureEntropy_probabilityMeasure (Ω := G)).comp continuous_fst
    simp [entropy_def]
  have obs₂ : Continuous
      (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ H[ id ; μ.2.toMeasure ]) := by
    convert (continuous_measureEntropy_probabilityMeasure (Ω := G)).comp continuous_snd
    simp [entropy_def]
  continuity

lemma continuous_rdist_restrict_probabilityMeasure₁
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    (X : Ω → G) (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] (X_mble : Measurable X) :
    Continuous
      (fun (μ : ProbabilityMeasure G) ↦ d[id ; P.map X # id ; μ.toMeasure]) := by
  have obs : IsProbabilityMeasure (P.map X) := by
    refine ⟨by simp [Measure.map_apply X_mble MeasurableSet.univ]⟩
  let ι : ProbabilityMeasure G → ProbabilityMeasure G × ProbabilityMeasure G :=
      fun ν ↦ ⟨⟨P.map X, obs⟩, ν⟩
  have ι_cont : Continuous ι := Continuous.Prod.mk _
  convert continuous_rdist_restrict_probabilityMeasure.comp ι_cont

lemma rdist_eq_rdist_id_map : d[ X ; μ # Y ; μ' ] = d[ id ; μ.map X # id ; μ'.map Y ] := by
  simp only [rdist_def, entropy_def, Measure.map_id]

lemma continuous_rdist_restrict_probabilityMeasure₁'
    [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]
    (X : Ω → G) (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] (X_mble : Measurable X) :
    Continuous
      (fun (μ : ProbabilityMeasure G) ↦ d[ X ; P # id ; μ.toMeasure ]) := by
  simp only [@rdist_eq_rdist_id_map Ω G G mΩ P hG, Measure.map_id]
  exact continuous_rdist_restrict_probabilityMeasure₁ _ _ X_mble

/-- If $X', Y'$ are copies of $X, Y$ respectively then $d[X' ; Y']=d[X ; Y]$. -/
lemma ProbabilityTheory.IdentDistrib.rdist_eq {X' : Ω'' → G} {Y' : Ω''' →G}
    (hX : IdentDistrib X X' μ μ'') (hY : IdentDistrib Y Y' μ' μ''') :
    d[X ; μ # Y ; μ'] = d[X' ; μ'' # Y' ; μ'''] := by
  simp [rdist, hX.map_eq, hY.map_eq, hX.entropy_eq, hY.entropy_eq]

/--   If $X, Y$ are independent $G$-random variables then
  $$ d[X ; Y] := H[X - Y] - H[X]/2 - H[Y]/2.$$-/
lemma ProbabilityTheory.IndepFun.rdist_eq [IsFiniteMeasure μ]
    {Y : Ω → G} (h : IndepFun X Y μ) (hX : Measurable X) (hY : Measurable Y) :
    d[X ; μ # Y ; μ] = H[X-Y ; μ] - H[X ; μ]/2 - H[Y ; μ]/2 := by
  rw [rdist_def]
  congr 2
  have h_prod : (μ.map X).prod (μ.map Y) = μ.map (⟨ X, Y ⟩) :=
    ((indepFun_iff_map_prod_eq_prod_map_map hX hY).mp h).symm
  rw [h_prod, entropy_def, Measure.map_map (measurable_fst.sub measurable_snd) (hX.prod_mk hY)]
  rfl

/-- $$ d[X ; Y] = d[Y ; X].$$ -/
lemma rdist_symm [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    d[X ; μ # Y ; μ'] = d[Y ; μ' # X ; μ] := by
  rw [rdist_def, rdist_def, sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_neg (measurable_fst.sub measurable_snd)]
  have : (-fun x : G × G ↦ x.1 - x.2) = (fun x ↦ x.1 - x.2) ∘ Prod.swap := by ext ; simp
  rw [this, entropy_def, ← Measure.map_map (measurable_fst.sub measurable_snd) measurable_swap,
    Measure.prod_swap]
  rfl

-- note : many of the statements below probably need measurability hypotheses on X, Y, and/or guarantees that a measure is a probability measure.

/-- $$|H[X]-H[Y]| \leq 2 d[X ; Y].$$ -/
lemma diff_ent_le_rdist [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) :
    |H[X ; μ] - H[Y ; μ']| ≤ 2 * d[X ; μ # Y ; μ'] := by
  obtain ⟨ν, X', Y', _, hX', hY', hind, hIdX, hIdY⟩ := independent_copies hX hY μ μ'
  rw [← hIdX.rdist_eq hIdY, hind.rdist_eq hX' hY', ← hIdX.entropy_eq, ← hIdY.entropy_eq, abs_le]
  have := ent_of_indep_diff_lower hX' hY' hind
  constructor
  · linarith[le_max_right H[X'; ν] H[Y'; ν]]
  · linarith[le_max_left H[X'; ν] H[Y'; ν]]

/-- $$  H[X-Y] - H[X] \leq 2d[X ; Y].$$ -/
lemma diff_ent_le_rdist' [IsProbabilityMeasure μ] {Y : Ω → G}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ):
    H[X - Y ; μ] - H[X ; μ] ≤ 2 * d[X ; μ # Y ; μ] := by
  rw [h.rdist_eq hX hY]
  linarith[ent_of_indep_diff_lower hX hY h, le_max_right H[X; μ] H[Y; μ]]

/-- $$  H[X-Y] - H[Y] \leq 2d[X ; Y].$$ -/
lemma diff_ent_le_rdist'' [IsProbabilityMeasure μ] {Y : Ω → G}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) :
    H[X-Y ; μ] - H[Y ; μ] ≤ 2 * d[X ; μ # Y ; μ] := by
  rw [h.rdist_eq hX hY]
  linarith[ent_of_indep_diff_lower hX hY h, le_max_left H[X; μ] H[Y; μ]]

/--   $$ d[X ; Y] \geq 0.$$  -/
lemma rdist_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) : 0 ≤ d[X ; μ # Y ; μ'] := by
  linarith [ge_trans (diff_ent_le_rdist hX hY) (abs_nonneg (H[X ; μ] - H[Y ; μ']))]

/-- Adding a constant to a random variable does not change the Rusza distance. -/
lemma rdist_add_const [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) :
    d[X ; μ # (fun ω ↦ Y ω + c) ; μ'] = d[X ; μ # Y ; μ'] := by
  obtain ⟨ν, X', Y', _, hX', hY', hind, hIdX, hIdY⟩ := independent_copies hX hY μ μ'
  have A : IdentDistrib (fun ω ↦ Y' ω + c) (fun ω ↦ Y ω + c) ν μ' :=
    hIdY.comp (measurable_add_const c)
  have B : IndepFun X' (fun ω ↦ Y' ω + c) ν :=
    hind.comp measurable_id (measurable_add_const c)
  have C : X' - (fun ω ↦ Y' ω + c) = fun ω ↦ (X' - Y') ω + (-c) := by
    ext ω; simp;  abel
  rw [← hIdX.rdist_eq hIdY, ← hIdX.rdist_eq A, hind.rdist_eq hX' hY',
    B.rdist_eq hX' (hY'.add_const _), entropy_add_const _ _ hY', C, entropy_add_const]
  exact hX'.sub hY'

/-- The **improved entropic Ruzsa triangle inequality**. -/
lemma ent_of_diff_le (X : Ω → G) (Y : Ω → G) (Z : Ω → G)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : IndepFun (⟨ X, Y ⟩) Z μ) [IsProbabilityMeasure μ] :
    H[X - Y; μ] ≤ H[X - Z; μ] + H[Z - Y; μ] - H[Z; μ] := by
  have h1 : H[⟨X - Z, ⟨Y, X - Y⟩⟩; μ] + H[X - Y; μ] ≤ H[⟨X - Z, X - Y⟩; μ] + H[⟨Y, X - Y⟩; μ] :=
    entropy_triple_add_entropy_le μ (hX.sub hZ) hY (hX.sub hY)
  have h2 : H[⟨X - Z, X - Y⟩ ; μ] ≤ H[X - Z ; μ] + H[Y - Z ; μ] := by
    calc H[⟨X - Z, X - Y⟩ ; μ] ≤ H[⟨X - Z, Y - Z⟩ ; μ] := by
          have : ⟨X - Z, X - Y⟩ = (fun p ↦ (p.1, p.1 - p.2)) ∘ ⟨X - Z, Y - Z⟩ := by ext1; simp
          rw [this]
          exact entropy_comp_le μ ((hX.sub hZ).prod_mk (hY.sub hZ)) _
    _ ≤ H[X - Z ; μ] + H[Y - Z ; μ] := by
          have h : 0 ≤ H[X - Z ; μ] + H[Y - Z ; μ] - H[⟨X - Z, Y - Z⟩ ; μ] :=
            mutualInformation_nonneg (hX.sub hZ) (hY.sub hZ) μ
          linarith
  have h3 : H[⟨ Y, X - Y ⟩ ; μ] ≤ H[⟨ X, Y ⟩ ; μ] := by
    have : ⟨Y, X - Y⟩ = (fun p ↦ (p.2, p.1 - p.2)) ∘ ⟨X, Y⟩ := by ext1; simp
    rw [this]
    exact entropy_comp_le μ (hX.prod_mk hY) _
  have h4 : H[⟨X - Z, ⟨Y, X - Y⟩⟩; μ] = H[⟨X, ⟨Y, Z⟩⟩ ; μ] := by
    refine entropy_of_comp_eq_of_comp μ ((hX.sub hZ).prod_mk (hY.prod_mk (hX.sub hY)))
      (hX.prod_mk (hY.prod_mk hZ))
      (fun p : G × (G × G) ↦ (p.2.2 + p.2.1, p.2.1, -p.1 + p.2.2 + p.2.1))
      (fun p : G × G × G ↦ (p.1 - p.2.2, p.2.1, p.1 - p.2.1)) ?_ ?_
    · ext1; simp
    · ext1; simp
  have h5 : H[⟨X, ⟨Y, Z⟩⟩ ; μ] = H[⟨X, Y⟩ ; μ] + H[Z ; μ] := by
    rw [entropy_assoc hX hY hZ, entropy_pair_eq_add (hX.prod_mk hY) hZ]
    exact h
  rw [h4, h5] at h1
  calc H[X - Y; μ] ≤ H[X - Z; μ] + H[Y - Z; μ] - H[Z; μ] := by linarith
  _ = H[X - Z; μ] + H[Z - Y; μ] - H[Z; μ] := by
    congr 2
    rw [entropy_sub_comm hY hZ]

/-- The **entropic Ruzsa triangle inequality** -/
lemma rdist_triangle {Ω Ω' Ω'' : Type u}
  [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
  [mΩ' : MeasurableSpace Ω'] (μ' : Measure Ω')
  [mΩ'' : MeasurableSpace Ω''] (μ'' : Measure Ω'')
  {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}
  (hX: Measurable X) (hY: Measurable Y) (hZ : Measurable Z)
  [hμ : IsProbabilityMeasure μ] [hμ' : IsProbabilityMeasure μ'] [hμ'' : IsProbabilityMeasure μ''] :
    d[X ; μ # Z ; μ''] ≤ d[X ; μ # Y ; μ'] + d[Y ; μ' # Z ; μ''] := by
  obtain ⟨A, mA, μA, X', Y', Z', hμA, hInd, hX', hY', hZ', H⟩ :=
    independent_copies3_nondep hX hY hZ μ μ' μ''
  suffices : d[ X' ; μA # Z' ; μA ] ≤ d[ X' ; μA # Y' ; μA ] + d[ Y' ; μA # Z' ; μA ]
  { rwa [ProbabilityTheory.IdentDistrib.rdist_eq H.left H.right.left,
      ProbabilityTheory.IdentDistrib.rdist_eq H.right.left H.right.right,
      ProbabilityTheory.IdentDistrib.rdist_eq H.left H.right.right] at this }
  have IndepLem: IndepFun (⟨ X', Z' ⟩) Y' μA
  · exact iIndepFun.indepFun_prod hInd (fun i => by fin_cases i ; all_goals { simpa }) 0 2 1
      (by norm_cast) (by norm_cast)
  calc d[ X' ; μA # Z' ; μA ] = H[X' - Z'; μA] - (H[X'; μA] / 2 + H[Z'; μA] / 2) := by
        rw [ProbabilityTheory.IndepFun.rdist_eq
          (by simpa using (iIndepFun.indepFun hInd (show 0 ≠ 2 by norm_cast))) hX' hZ'] ; ring
    _  ≤ (H[X' - Y' ; μA] + H[Y' - Z' ; μA] - H[Y' ; μA]) - (H[X'; μA] / 2 + H[Z'; μA] / 2) :=
          sub_le_sub_right (ent_of_diff_le _ _ _ hX' hZ' hY' IndepLem) _
    _ = (H[X' - Y' ; μA] - H[X'; μA] / 2 - H[Y' ; μA] / 2) +
          (H[Y' - Z' ; μA] - H[Y' ; μA] / 2 -  H[Z'; μA] / 2) := by ring
    _ = d[ X' ; μA # Y' ; μA ] + d[ Y' ; μA # Z' ; μA ] := by
        rw [ProbabilityTheory.IndepFun.rdist_eq (by simpa using (iIndepFun.indepFun hInd
          (show 0 ≠ 1 by norm_cast))) hX' hY', ProbabilityTheory.IndepFun.rdist_eq
          (by simpa using (iIndepFun.indepFun hInd (show 1 ≠ 2 by norm_cast))) hY' hZ']

/-- The conditional Ruzsa distance `d[X|Z ; Y|W]`. -/
noncomputable
def cond_rdist (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) : ℝ :=
  dk[condEntropyKernel X Z μ ; μ.map Z # condEntropyKernel Y W μ' ; μ'.map W]

@[inherit_doc cond_rdist]
notation3:max "d[" X " | " Z " ; " μ " # " Y " | " W " ; " μ'"]" => cond_rdist X Z Y W μ μ'

@[inherit_doc cond_rdist]
notation3:max "d[" X " | " Z " # " Y " | " W " ]" => cond_rdist X Z Y W volume volume

lemma cond_rdist_def (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω) (μ' : Measure Ω') :
    d[X | Z ; μ # Y | W ; μ']
      = dk[condEntropyKernel X Z μ ; μ.map Z # condEntropyKernel Y W μ' ; μ'.map W] := rfl

/-- The conditional Ruzsa distance `d[X ; Y|W]`. -/
noncomputable
def cond_rdist' (X : Ω → G) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) : ℝ :=
  dk[kernel.const Unit (μ.map X) ; Measure.dirac () # condEntropyKernel Y W μ' ; μ'.map W]

@[inherit_doc cond_rdist']
notation3:max "d[" X " ; " μ " # " Y " | " W " ; " μ' "]" => cond_rdist' X Y W μ μ'
@[inherit_doc cond_rdist']
notation3:max "d[" X " # " Y " | " W "]" => cond_rdist' X Y W volume volume

lemma cond_rdist'_def (X : Ω → G) (Y : Ω' → G) (W : Ω' → T) (μ : Measure Ω) (μ' : Measure Ω') :
    d[X ; μ # Y | W ; μ'] =
      dk[kernel.const Unit (μ.map X) ; Measure.dirac () # condEntropyKernel Y W μ' ; μ'.map W] := rfl

lemma cond_rdist_of_const {X : Ω → G} (hX : Measurable X) (Y : Ω' → G) (W : Ω' → T) (c : S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    d[X|(fun _ => c) ; μ # Y | W ; μ'] = d[X ; μ # Y | W ; μ'] := by
  have hcX : Measurable (fun ω => (c, X ω)) := by simp [measurable_prod, hX]
  have hc : MeasurableSet (Prod.fst ⁻¹' {c} : Set (S × G)) := measurable_fst (by simp)
  rw [cond_rdist_def, cond_rdist'_def, Measure.map_const,measure_univ,one_smul, kernel.rdist,
    kernel.rdist, integral_prod,integral_dirac,integral_prod,integral_dirac]
  dsimp; congr; ext x; congr
  rw [condEntropyKernel, kernel.comap_apply, kernel.condKernel_apply_of_ne_zero _ _ _]
  ext s hs
  rw [Measure.map_apply measurable_snd hs, kernel.const_apply, kernel.const_apply, cond_apply _ hc,
    Measure.map_apply hcX hc, Measure.map_apply hcX (hc.inter (measurable_snd hs)),
    Set.preimage_preimage, Set.preimage_inter, Set.preimage_preimage, Set.preimage_preimage,
    Set.preimage_const_of_mem (by rfl), measure_univ, inv_one, one_mul, Set.univ_inter,
    Measure.map_apply hX hs]
  rw [kernel.const_apply,Measure.map_apply hcX hc,Set.preimage_preimage]
  all_goals simp

lemma condKernel_eq_prod_of_indepFun {X : Ω → G} {Z : Ω → S} {Y : Ω → G} {W : Ω → T}
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun (⟨X, Z⟩) (⟨ Y, W ⟩) μ) :
    condEntropyKernel (⟨X, Y⟩) (⟨Z, W⟩) μ
      =ᵐ[μ.map (⟨Z, W⟩)] kernel.prodMkRight (condEntropyKernel X Z μ) T
        ×ₖ kernel.prodMkLeft S (condEntropyKernel Y W μ) := by
  have : IsMarkovKernel (condEntropyKernel X Z μ) := isMarkovKernel_condEntropyKernel hX hZ μ
  have : IsMarkovKernel (condEntropyKernel Y W μ) := isMarkovKernel_condEntropyKernel hY hW μ
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  sorry

/-- If $(X,Z)$ and $(Y,W)$ are independent, then
$$  d[X  | Z ; Y | W] = H[X'-Y'|Z', W'] - H[X'|Z']/2 - H[Y'|W']/2$$
-/
lemma cond_rdist_of_indep
    {X : Ω → G} {Z : Ω → S} {Y : Ω → G} {W : Ω → T}
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : IndepFun (⟨X, Z⟩) (⟨ Y, W ⟩) μ) :
    d[X | Z ; μ # Y | W ; μ] = H[X-Y | ⟨ Z, W ⟩ ; μ] - H[X | Z ; μ]/2 - H[Y | W ; μ]/2 := by
  have : IsMarkovKernel (condEntropyKernel X Z μ) := isMarkovKernel_condEntropyKernel hX hZ μ
  have : IsMarkovKernel (condEntropyKernel Y W μ) := isMarkovKernel_condEntropyKernel hY hW μ
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  rw[cond_rdist_def, kernel.rdist_eq', condEntropy_eq_kernel_entropy, condEntropy_eq_kernel_entropy,
    condEntropy_eq_kernel_entropy]
  rotate_left
  · exact hY
  · exact hW
  · exact hX
  · exact hZ
  · exact hX.sub hY
  · exact hZ.prod_mk hW
  congr 2
  have hZW : IndepFun Z W μ := by
    have h' := IndepFun.comp h measurable_snd measurable_snd
    exact h'
  have hZW_map : μ.map (⟨Z, W⟩) = (μ.map Z).prod (μ.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map hZ hW).mp hZW
  rw [← hZW_map]
  refine kernel.entropy_congr ?_
  have : kernel.map (condEntropyKernel (⟨X, Y⟩) (⟨Z, W⟩) μ) (fun x ↦ x.1 - x.2) measurable_sub
      =ᵐ[μ.map (⟨Z, W⟩)] condEntropyKernel (X - Y) (⟨Z, W⟩) μ :=
    (condEntropyKernel_comp (hX.prod_mk hY) (hZ.prod_mk hW) _ _).symm
  refine (this.symm.trans ?_).symm
  suffices kernel.prodMkRight (condEntropyKernel X Z μ) T
        ×ₖ kernel.prodMkLeft S (condEntropyKernel Y W μ)
      =ᵐ[μ.map (⟨Z, W⟩)] condEntropyKernel (⟨X, Y⟩) (⟨Z, W⟩) μ by
    filter_upwards [this] with x hx
    rw [kernel.map_apply, kernel.map_apply, hx]
  exact (condKernel_eq_prod_of_indepFun hX hZ hY hW μ h).symm

lemma cond_rdist'_of_indep {X : Ω → G} {Y : Ω → G} {W : Ω → T}
    (h : IndepFun X (⟨ Y, W ⟩) μ) :
    d[X ; μ # Y | W ; μ] = H[X-Y | W ; μ] - H[X ; μ]/2 - H[Y | W ; μ]/2 := by sorry

lemma cond_rdist_of_copy
    {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T}
    {X' : Ω'' → G} {Z' : Ω'' → S} {Y' : Ω''' → G} {W' : Ω''' → T}
    (h1 : IdentDistrib (⟨X, Z⟩) (⟨X', Z'⟩) μ μ'') (h2 : IdentDistrib (⟨Y, W⟩) (⟨Y', W'⟩) μ' μ''') :
    d[X | Z ; μ # Y | W ; μ'] = d[X' | Z' ; μ'' # Y' | W' ; μ'''] := by sorry

lemma cond_rdist'_of_copy
    {X : Ω → G} {Y : Ω' → G} {W : Ω' → T} {X' : Ω'' → G} {Y' : Ω''' → G} {W' : Ω''' → T}
    (h1 : IdentDistrib X X' μ μ'') (h2 : IdentDistrib (⟨Y, W⟩) (⟨Y', W'⟩) μ' μ''') :
    d[X ; μ # Y | W ; μ'] = d[X' ; μ'' # Y' | W' ; μ'''] := by sorry


/-- The **Kaimonovich-Vershik inequality**. $$H[X + Y + Z] - H[X + Y] \leq H[Y+Z] - H[Y].$$ -/
lemma kaimonovich_vershik {X Y Z : Ω → G} (h : iIndepFun (fun _ ↦ hG) ![X, Y, Z] μ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [IsProbabilityMeasure μ] :
    H[X + Y + Z ; μ] - H[X + Y ; μ] ≤ H[Y + Z ; μ] - H[Y ; μ] := by
  suffices : (H[X ; μ] + H[Y ; μ] + H[Z ; μ]) + H[X + Y + Z ; μ]
    ≤ (H[X ; μ] + H[Y + Z ; μ]) + (H[Z ; μ] + H[X + Y ; μ])
  . linarith
  have : ∀ (i : Fin 3), Measurable (![X, Y, Z] i) := fun i ↦ by fin_cases i <;> assumption
  convert entropy_triple_add_entropy_le _ hX hZ (show Measurable (X + (Y+Z)) by measurability) using 2
  . calc
      H[X ; μ] + H[Y ; μ] + H[Z ; μ] = H[⟨ X, Y ⟩ ; μ] + H[Z ; μ] := by
        congr 1
        symm ; apply entropy_pair_eq_add' hX hY
        convert iIndepFun.indepFun h (show 0 ≠ 1 by decide)
      _ = H[⟨ ⟨ X, Y ⟩, Z ⟩ ; μ] := by
        symm ; apply entropy_pair_eq_add' (Measurable.prod_mk hX hY) hZ
        exact iIndepFun.indepFun_prod h this 0 1 2 (by decide) (by decide)
      _ = H[⟨ X, ⟨ Z , X + (Y+Z) ⟩ ⟩ ; μ] := by
        apply entropy_of_comp_eq_of_comp μ (by measurability) (by measurability) (fun ((x, y), z) ↦ (x, (z, x+y+z))) (fun (a, (b, c)) ↦ ((a, c-a-b), b))
        all_goals { funext ω ; dsimp [prod] ; ext <;> dsimp ; abel }
  . rw [add_assoc]
  . refine entropy_pair_eq_add' hX (hY.add hZ) ?_ |>.symm.trans ?_
    . apply IndepFun.symm
      exact iIndepFun.add h this 1 2 0 (by decide) (by decide)
    symm
    exact entropy_of_shear_eq hX (hY.add hZ)
  refine entropy_pair_eq_add' hZ (hX.add hY) ?_ |>.symm.trans ?_
  . apply IndepFun.symm
    exact iIndepFun.add h this 0 1 2 (by decide) (by decide)
  rw [show X + (Y + Z) = Z + (X + Y) by abel]
  symm
  exact entropy_of_shear_eq hZ (hX.add hY)

/-- A version of  **Kaimonovich-Vershik inequality** with some variables negated -/
lemma kaimonovich_vershik' {X Y Z : Ω → G} (h : iIndepFun (fun _ ↦ hG) ![X, Y, Z] μ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [IsProbabilityMeasure μ] :
    H[X - (Y + Z) ; μ] - H[X - Y ; μ] ≤ H[Y + Z ; μ] - H[Y ; μ] := by
  rw [← entropy_neg (hY.add' hZ), ← entropy_neg hY]
  simp_rw [sub_eq_add_neg, neg_add, ← add_assoc]
  apply kaimonovich_vershik _ hX hY.neg hZ.neg
  convert (h.neg 1).neg 2
  ext i; fin_cases i
  · simp (discharger := decide)
  · simp (discharger := decide)
  · rw [← show ∀ h : 2 < 3, (2 : Fin 3) = ⟨2, h⟩ by intro; rfl]
    simp (discharger := decide)



section BalogSzemerediGowers

/--  The **entropic Balog-Szemerédi-Gowers inequality**. Let $A, B$ be $G$-valued random variables
on $\Omega$, and set $Z \coloneq A+B$. Then
$$\sum_{z} P[Z=z] d[(A | Z = z) ; (B | Z = z)] \leq 3 I[A :B] + 2 H[Z] - H[A] - H[B]. $$ -/
lemma ent_bsg : 0 = 1 := by sorry


end BalogSzemerediGowers

variable (μ μ') in
/--   Suppose that $(X, Z)$ and $(Y, W)$ are random variables, where $X, Y$ take values in an abelian group. Then
$$   d[X  | Z ; Y | W] \leq d[X ; Y] + \tfrac{1}{2} I[X : Z] + \tfrac{1}{2} I[Y : W].$$
-/
lemma condDist_le [Fintype S] [Fintype T] {X : Ω → G} {Z : Ω → S} {Y : Ω' → G} {W : Ω' → T}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty S]
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y) (hW : Measurable W) :
      d[X | Z ; μ # Y|W ; μ'] ≤ d[X ; μ # Y ; μ'] + I[X : Z ; μ]/2 + I[Y : W ; μ']/2 := by
  have hXZ : Measurable (⟨X, Z⟩ : Ω → G × S):= Measurable.prod_mk hX hZ
  have hYW : Measurable (⟨Y, W⟩ : Ω' → G × T):= Measurable.prod_mk hY hW
  obtain ⟨ν, XZ', YW', _, hXZ', hYW', hind, hIdXZ, hIdYW⟩ := independent_copies hXZ hYW μ μ'
  let X' := Prod.fst ∘ XZ'
  let Z' := Prod.snd ∘ XZ'
  let Y' := Prod.fst ∘ YW'
  let W' := Prod.snd ∘ YW'
  have hX' : Measurable X' := hXZ'.fst
  have hZ' : Measurable Z' := hXZ'.snd
  have hY' : Measurable Y' := hYW'.fst
  have hW' : Measurable W' := hYW'.snd
  have hind' : IndepFun X' Y' ν := IndepFun.comp hind measurable_fst measurable_fst
  rw [show XZ' = ⟨X', Z'⟩ by rfl] at hIdXZ hind
  rw [show YW' = ⟨Y', W'⟩ by rfl] at hIdYW hind
  rw [←cond_rdist_of_copy hIdXZ hIdYW, cond_rdist_of_indep hX' hZ' hY' hW' _ hind]
  have hIdX : IdentDistrib X X' μ ν := hIdXZ.symm.comp measurable_fst
  have hIdY : IdentDistrib Y Y' μ' ν := hIdYW.symm.comp measurable_fst
  rw [IdentDistrib.rdist_eq (μ'' := ν) (μ''' := ν) hIdX hIdY]
  rw [hIdXZ.symm.mutualInformation_eq, hIdYW.symm.mutualInformation_eq]
  rw [IndepFun.rdist_eq hind' hX' hY',
  mutualInformation_eq_entropy_sub_condEntropy hX' hZ',
  mutualInformation_eq_entropy_sub_condEntropy hY' hW']
  have h := condEntropy_le_entropy ν (X := X' - Y') (Y := (⟨Z',W'⟩)) (hX'.sub hY') (Measurable.prod hZ' hW')
  linarith [h,entropy_nonneg Z' ν,entropy_nonneg W' ν]

variable (μ μ') in
lemma condDist_le' [Fintype T] {X : Ω → G} {Y : Ω' → G} {W : Ω' → T}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) :
    d[X ; μ # Y|W ; μ'] ≤ d[X ; μ # Y ; μ'] + I[Y : W ; μ']/2 := by
  rw [←cond_rdist_of_const hX _ _ (0 : Fin 1)]
  refine' (condDist_le μ μ' hX measurable_const hY hW).trans _
  simp [mutualInformation_const hX (0 : Fin 1)]

variable (μ) in
lemma comparison_of_ruzsa_distances
    {Ω' : Type u} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ') :
    d[X; μ # Y+Z ; μ'] - d[X; μ # Y ; μ'] ≤ (H[Y + Z; μ'] - H[Y; μ']) / 2 ∧
    (ElementaryAddCommGroup G 2 →
      H[Y + Z; μ'] - H[Y; μ'] = d[Y; μ' # Z; μ'] + H[Z; μ'] / 2 - H[Y; μ'] / 2) := by
  obtain ⟨Ω'', mΩ'', μ'', X', Y', Z', hμ, hi, hX', hY', hZ', h2X', h2Y', h2Z'⟩ :=
    independent_copies3_nondep hX hY hZ μ μ' μ'
  have hY'Z' : IndepFun Y' Z' μ'' := hi.indepFun (show (1 : Fin 3) ≠ 2 by decide)
  have h2 : IdentDistrib (Y' + Z') (Y + Z) μ'' μ' := h2Y'.add h2Z' hY'Z' h
  have hm : ∀ (i : Fin 3), Measurable (![X', Y', Z'] i) :=
    fun i ↦ by fin_cases i <;> (dsimp; assumption)
  have hXY' : IndepFun X' Y' μ'' := hi.indepFun (show (0 : Fin 3) ≠ 1 by decide)
  have hYZ' : IndepFun Y' Z' μ'' := hi.indepFun (show (1 : Fin 3) ≠ 2 by decide)
  have hXYZ' : IndepFun X' (Y' + Z') μ'' := by
    symm
    exact hi.add hm 1 2 0 (by decide) (by decide)
  rw [← h2X'.rdist_eq h2Y', ← h2X'.rdist_eq h2, ← h2Y'.rdist_eq h2Z',
    ← h2.entropy_eq, ← h2Y'.entropy_eq, ← h2Z'.entropy_eq]
  rw [hXY'.rdist_eq hX' hY', hYZ'.rdist_eq hY' hZ', hXYZ'.rdist_eq hX' (hY'.add hZ')]
  constructor
  · linarith [kaimonovich_vershik' hi hX' hY' hZ']
  · intro hG
    rw [pi.sub_eq_add Y' Z']
    ring

variable (μ) in
/-- Let $X, Y, Z$ be random variables taking values in some abelian group, and with $Y, Z$ independent. Then we have
  $$ d[X ; Y + Z] -d[X ; Y]  \leq \tfrac{1}{2} (H[Y+Z] - H[Y]) $$
  $$ = \tfrac{1}{2} d[Y ; Z] + \tfrac{1}{4} H[Z] - \tfrac{1}{4} H[Y]$$
  and
$$
  d[X ; Y|Y+Z] - d[X ; Y] \leq \tfrac{1}{2} \bigl(H[Y+Z] - H[Z]\bigr) $$
$$   = \tfrac{1}{2} d[Y ; Z] + \tfrac{1}{4} H[Y] - \tfrac{1}{4} H[Z].$$
-/
/- Note: we currently assume `Ω` and `Ω'` live in the same universe. -/
lemma condDist_diff_le {Ω' : Type u} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ') :
    d[X; μ # Y+Z ; μ'] - d[X; μ # Y ; μ'] ≤ (H[Y + Z; μ'] - H[Y; μ']) / 2 :=
  (comparison_of_ruzsa_distances μ hX hY hZ h).1

variable (μ) [ElementaryAddCommGroup G 2] in
lemma entropy_sub_entropy_eq_condDist_add {Ω' : Type u} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ') :
    H[Y + Z; μ'] - H[Y; μ'] = d[Y; μ' # Z; μ'] + H[Z; μ'] / 2 - H[Y; μ'] / 2 :=
  (comparison_of_ruzsa_distances μ hX hY hZ h).2 ‹_›

variable (μ) [ElementaryAddCommGroup G 2] in
lemma condDist_diff_le' {Ω' : Type u} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ') :
    d[X; μ # Y + Z; μ'] - d[X; μ # Y; μ'] ≤
    d[Y; μ' # Z; μ'] / 2 + H[Z; μ'] / 4 - H[Y; μ'] / 4 := by
  linarith [condDist_diff_le μ hX hY hZ h, entropy_sub_entropy_eq_condDist_add μ hX hY hZ h]

variable (μ) in
lemma condDist_diff_le'' {Ω' : Type u} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ') :
    d[X ; μ # Y|Y+Z ; μ'] - d[X ; μ # Y ; μ'] ≤ (H[Y+Z ; μ'] - H[Z ; μ'])/2 := by
  rw [← mutualInformation_add_right hY hZ h]
  linarith [condDist_le' μ μ' hX hY (hY.add' hZ)]

variable (μ) [ElementaryAddCommGroup G 2] in
lemma condDist_diff_le''' {Ω' : Type u} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (h : IndepFun Y Z μ') :
    d[X ; μ # Y|Y+Z ; μ'] - d[X ; μ # Y ; μ'] ≤
    d[Y ; μ' # Z ; μ']/2 + H[Y ; μ']/4 - H[Z ; μ']/4 := by
  linarith [condDist_diff_le'' μ hX hY hZ h, entropy_sub_entropy_eq_condDist_add μ hX hY hZ h]


variable (μ) in
lemma condDist_diff_ofsum_le {Ω' : Type u} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : Ω → G} {Y Z Z' : Ω' → G}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hZ' : Measurable Z')
    (h : iIndepFun (fun _ ↦ hG) ![Y, Z, Z'] μ') :
    d[X ; μ # Y+Z | Y + Z + Z'; μ'] - d[X; μ # Y; μ'] ≤
    (H[Y + Z + Z'; μ'] + H[Y + Z; μ'] - H[Y ; μ'] - H[Z' ; μ'])/2 := by
  have hadd : IndepFun (Y + Z) Z' μ' :=
  (h.add (Fin.cases hY <| Fin.cases hZ <| Fin.cases hZ' Fin.rec0) 0 1 2
  (show 0 ≠ 2 by decide) (show 1 ≠ 2 by decide))
  have h1 := condDist_diff_le'' μ hX (show Measurable (Y + Z) by measurability) hZ' hadd
  have h2 := condDist_diff_le μ hX hY hZ (h.indepFun (show 0 ≠ 1 by decide))
  linarith [h1, h2]
