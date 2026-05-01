module

public import Mathlib.Probability.IdentDistrib
public import PFR.ForMathlib.Entropy.Basic
public import PFR.ForMathlib.FiniteRange.Defs
public import PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog
public import PFR.Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Kullback-Leibler divergence

Definition of Kullback-Leibler divergence and basic facts
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

variable {Ω Ω' Ω'' Ω''' G : Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G]

variable {X : Ω → G} {Y : Ω' → G}

/-- If `X, Y` are two `G`-valued random variables, the Kullback--Leibler divergence is defined as
  `KL(X ‖ Y) := ∑ₓ 𝐏(X = x) log (𝐏(X = x) / 𝐏(Y = x))`.

Note that this definition only makes sense when `X` is absolutely continuous wrt to `Y`,
i.e., `∀ x, 𝐏(Y = x) = 0 → 𝐏(X = x) = 0`. Otherwise, the divergence should be infinite, but since
we use real numbers for ease of computations, this is not a possible choice. -/
noncomputable def KLDiv (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  ∑' x, (μ.map X).real {x} * log ((μ.map X).real {x} / ((μ'.map Y).real {x}))

@[inherit_doc KLDiv] notation3:max "KL[" X " ; " μ " # " Y " ; " μ' "]" => KLDiv X Y μ μ'

@[inherit_doc KLDiv] notation3:max "KL[" X " # " Y "]" => KLDiv X Y volume volume

@[simp] lemma KLDiv_self : KL[X ; μ # X ; μ] = 0 := by simp [KLDiv]

/-- If `X'` is a copy of `X`, and `Y'` is a copy of `Y`, then `KL(X' ‖ Y') = KL(X ‖ Y)`. -/
lemma ProbabilityTheory.IdentDistrib.KLDiv_eq (X' : Ω'' → G) (Y' : Ω''' → G)
    (hX : IdentDistrib X X' μ μ'') (hY : IdentDistrib Y Y' μ' μ''') :
    KL[X ; μ # Y ; μ'] = KL[X' ; μ'' # Y' ; μ'''] := by
  simp only [KLDiv]
  congr with x
  congr
  · exact hX.map_eq
  · exact hX.map_eq
  · exact hY.map_eq

lemma KLDiv_eq_sum [Fintype G] :
    KL[X ; μ # Y ; μ'] =
      ∑ x, (μ.map X).real {x} * log ((μ.map X).real {x} / ((μ'.map Y).real {x})) :=
  tsum_eq_sum (by simp)

lemma KLDiv_eq_sum_negMulLog [Fintype G] :
    KL[X ; μ # Y ; μ'] = ∑ x, - (μ'.map Y).real {x} *
      negMulLog ((μ.map X).real {x} / ((μ'.map Y).real {x})) := by
  rw [KLDiv_eq_sum]
  congr with g
  rcases eq_or_ne ((μ.map X).real {g}) 0 with h | h
  · simp [h]
  rcases eq_or_ne ((μ'.map Y).real {g}) 0 with h' | h'
  · simp [h']
  simp only [negMulLog, ← mul_assoc]
  field_simp

/-- `KL(X ‖ Y) ≥ 0`. -/
lemma KLDiv_nonneg [Finite G] [MeasurableSingletonClass G] [IsZeroOrProbabilityMeasure μ]
    [IsZeroOrProbabilityMeasure μ'] (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, μ'.map Y {x} = 0 → μ.map X {x} = 0) : 0 ≤ KL[X ; μ # Y ; μ'] := by
  cases nonempty_fintype G
  rw [KLDiv_eq_sum]
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ' with rfl | hμ'
  · simp
  apply le_trans ?_ (sum_mul_log_div_leq (by simp) (by simp) ?_)
  · have : IsProbabilityMeasure (μ'.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
    have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
    simp
  · intro i _ hi
    simp only [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] at hi
    simp [Measure.real, habs i hi]


/-- `KL(X ‖ Y) = 0` if and only if `Y` is a copy of `X`. -/
lemma KLDiv_eq_zero_iff_identDistrib [Finite G] [MeasurableSingletonClass G]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, (μ'.map Y).real {x} = 0 → (μ.map X).real {x} = 0) :
    KL[X ; μ # Y ; μ'] = 0 ↔ IdentDistrib X Y μ μ' := by
  cases nonempty_fintype G
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [KLDiv, h.map_eq]⟩
  let νY := μ'.map Y
  have : IsProbabilityMeasure νY := Measure.isProbabilityMeasure_map hY.aemeasurable
  let νX := μ.map X
  have : IsProbabilityMeasure νX := Measure.isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨r, hr⟩ : ∃ (r : ℝ), ∀ x ∈ Finset.univ, (νX.real {x}) = r * νY.real {x} := by
    apply sum_mul_log_div_eq_iff (by simp) (by simp) fun i _ hi ↦ ?_
    · simpa [KLDiv_eq_sum] using h
    · simp [habs i hi, νX]
  have r_eq : r = 1 := by
    have : r * ∑ x, νY.real {x} = ∑ x, νX.real {x} := by
      simp only [Finset.mul_sum, Finset.mem_univ, hr]
    simpa using this
  have : νX = νY := by
    apply Measure.ext_iff_singleton.mpr (fun x ↦ ?_)
    simpa [Measure.real, r_eq, ENNReal.toReal_eq_toReal_iff'] using hr x (Finset.mem_univ _)
  exact ⟨hX.aemeasurable, hY.aemeasurable, this⟩

/-- If $S$ is a finite set, $w_s$ is non-negative,
and ${\bf P}(X=x) = \sum_{s\in S} w_s {\bf P}(X_s=x)$, ${\bf P}(Y=x) =
  \sum_{s\in S} w_s {\bf P}(Y_s=x)$ for all $x$, then
$$D_{KL}(X\Vert Y) \le \sum_{s\in S} w_s D_{KL}(X_s\Vert Y_s).$$ -/
lemma KLDiv_of_convex [Finite G]
    {ι : Type*} {S : Finset ι} {w : ι → ℝ} (hw : ∀ s ∈ S, 0 ≤ w s)
    (X' : ι → Ω'' → G) (Y' : ι → Ω''' → G)
    (hconvex : ∀ x, (μ.map X).real {x} = ∑ s ∈ S, w s * (μ''.map (X' s)).real {x})
    (hconvex' : ∀ x, (μ'.map Y).real {x} = ∑ s ∈ S, w s * (μ'''.map (Y' s)).real {x})
    (habs : ∀ s ∈ S, ∀ x, (μ'''.map (Y' s)).real {x} = 0 → (μ''.map (X' s)).real {x} = 0) :
    KL[X ; μ # Y ; μ'] ≤ ∑ s ∈ S, w s * KL[X' s ; μ'' # Y' s ; μ'''] := by
  cases nonempty_fintype G
  conv_lhs => rw [KLDiv_eq_sum]
  have A x : (μ.map X).real {x} * log ((μ.map X).real {x} / ((μ'.map Y).real {x}))
    ≤ ∑ s ∈ S, (w s * (μ''.map (X' s)).real {x}) *
        log ((w s * (μ''.map (X' s)).real {x}) / (w s * ((μ'''.map (Y' s)).real {x}))) := by
    rw [hconvex, hconvex']
    apply sum_mul_log_div_leq (fun s hs ↦ ?_) (fun s hs ↦ ?_) (fun s hs h's ↦ ?_)
    · exact mul_nonneg (by simp [hw s hs]) (by simp)
    · exact mul_nonneg (by simp [hw s hs]) (by simp)
    · rcases mul_eq_zero.1 h's with h | h
      · simp [h]
      · simp [habs s hs x h]
  have B x : (μ.map X).real {x} * log ((μ.map X).real {x} / ((μ'.map Y).real {x}))
    ≤ ∑ s ∈ S, (w s * (μ''.map (X' s)).real {x}) *
        log ((μ''.map (X' s)).real {x} / ((μ'''.map (Y' s)).real {x})) := by
    apply (A x).trans_eq
    apply Finset.sum_congr rfl (fun s _ ↦ ?_)
    rcases eq_or_ne (w s) 0 with h's | h's
    · simp [h's]
    · congr 2
      rw [mul_div_mul_left _ _ h's]
  apply (Finset.sum_le_sum (fun x _ ↦ B x)).trans_eq
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, KLDiv_eq_sum]

/-- If $f:G \to H$ is an injection, then $D_{KL}(f(X)\Vert f(Y)) = D_{KL}(X\Vert Y)$. -/
lemma KLDiv_of_comp_inj {H : Type*} [MeasurableSpace H] [DiscreteMeasurableSpace G]
    [MeasurableSingletonClass H] {f : G → H}
    (hf : Function.Injective f) (hX : Measurable X) (hY : Measurable Y) :
    KL[f ∘ X ; μ # f ∘ Y ; μ'] = KL[X ; μ # Y ; μ'] := by
  simp only [KLDiv]
  rw [← hf.tsum_eq]
  · symm
    congr with x
    have A : (Measure.map X μ) {x} = (Measure.map (f ∘ X) μ) {f x} := by
      rw [Measure.map_apply, Measure.map_apply]
      · rw [Set.preimage_comp, ← Set.image_singleton, Set.preimage_image_eq _ hf]
      · exact .comp .of_discrete hX
      · exact measurableSet_singleton (f x)
      · exact hX
      · exact measurableSet_singleton x
    have B : (Measure.map Y μ') {x} = (Measure.map (f ∘ Y) μ') {f x} := by
      rw [Measure.map_apply, Measure.map_apply]
      · congr
        exact Set.Subset.antisymm (fun ⦃a⦄ ↦ congrArg f) fun ⦃a⦄ a_1 ↦ hf a_1
      · exact .comp .of_discrete hY
      · exact measurableSet_singleton (f x)
      · exact hY
      · exact measurableSet_singleton x
    simp [A, B, measureReal_def]
  · intro y hy
    have : (μ.map (f ∘ X)).real {y} ≠ 0 := by
      intro h
      simp [h] at hy
    rw [map_measureReal_apply (.comp .of_discrete hX) (.singleton y)] at this
    have : f ∘ X ⁻¹' {y} ≠ ∅ := by
      intro h
      simp [h] at this
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 this
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff] at hz
    exact Set.mem_range.2 ⟨X z, hz⟩

lemma KLDiv_add_const [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X : Ω → G} {Y : Ω' → G} (hX : Measurable X) (hY : Measurable Y) (s : G) :
    KL[(fun ω ↦ X ω + s) ; μ # (fun ω ↦ Y ω + s) ; μ'] = KL[X ; μ # Y ; μ'] :=
  KLDiv_of_comp_inj (f := fun g ↦ g + s) (add_left_injective s) hX hY

open Set

open scoped Pointwise

/-- The distribution of `X + Z` is the convolution of the distributions of `Z` and `X` when these
random variables are independent.
Probably already available somewhere in some form, but I couldn't locate it. -/
lemma ProbabilityTheory.IndepFun.map_add_eq_sum
    [Fintype G] [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X Z : Ω → G} (h_indep : IndepFun X Z μ)
    (hX : Measurable X) (hZ : Measurable Z) (S : Set G) :
    μ.map (X + Z) S = ∑ s, μ.map Z {s} * μ.map X ({-s} + S) := by
  rw [Measure.map_apply (by fun_prop) (DiscreteMeasurableSpace.forall_measurableSet S)]
  have : (X + Z) ⁻¹' S = ⋃ s, X ⁻¹' ({-s} + S) ∩ Z ⁻¹' {s} := by
    apply Subset.antisymm
    · intro y hy
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨Z y, by simpa [add_comm] using hy, rfl⟩
    · simp only [iUnion_subset_iff]
      intro i y hy
      simp only [singleton_add, image_add_left, neg_neg, mem_inter_iff, mem_preimage,
        mem_singleton_iff] at hy
      simp [hy.1, hy.2, add_comm]
  rw [this, measure_iUnion, tsum_fintype]; rotate_left
  · intro i j hij
    simp only [Function.onFun, singleton_add, image_add_left, neg_neg]
    apply Disjoint.inter_left'
    apply Disjoint.inter_right'
    apply disjoint_left.2 (fun a ha hb ↦ ?_)
    rw [← ha, ← hb] at hij
    exact hij rfl
  · intro i
    exact (hX (DiscreteMeasurableSpace.forall_measurableSet _)).inter
      (hZ (measurableSet_singleton _))
  congr with i
  rw [h_indep.measure_inter_preimage_eq_mul _ _ (DiscreteMeasurableSpace.forall_measurableSet _)
    (measurableSet_singleton _), mul_comm,
    Measure.map_apply hZ (measurableSet_singleton _),
    Measure.map_apply hX (DiscreteMeasurableSpace.forall_measurableSet _)]

/-- The distribution of `X + Z` is the convolution of the distributions of `Z` and `X` when these
random variables are independent.
Probably already available somewhere in some form, but I couldn't locate it. -/
lemma ProbabilityTheory.IndepFun.map_add_singleton_eq_sum
    [Fintype G] [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X Z : Ω → G} (h_indep : IndepFun X Z μ)
    (hX : Measurable X) (hZ : Measurable Z) (x : G) :
    μ.map (X + Z) {x} = ∑ s, μ.map Z {s} * μ.map X {x - s} := by
  rw [h_indep.map_add_eq_sum hX hZ]
  congr with s
  congr
  simp
  abel

lemma ProbabilityTheory.IndepFun.real_map_add_eq_sum [IsFiniteMeasure μ]
    [Fintype G] [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X Z : Ω → G} (h_indep : IndepFun X Z μ)
    (hX : Measurable X) (hZ : Measurable Z) (S : Set G) :
    (μ.map (X + Z)).real S = ∑ s, (μ.map Z).real {s} * (μ.map X).real ({-s} + S) := by
  rw [measureReal_def, h_indep.map_add_eq_sum hX hZ, ENNReal.toReal_sum (by finiteness)]
  congr with s
  simp only [singleton_add, image_add_left, neg_neg, ENNReal.toReal_mul]
  rfl

lemma ProbabilityTheory.IndepFun.real_map_add_singleton_eq_sum
    [Fintype G] [AddCommGroup G] [DiscreteMeasurableSpace G] [IsFiniteMeasure μ]
    {X Z : Ω → G} (h_indep : IndepFun X Z μ)
    (hX : Measurable X) (hZ : Measurable Z) (x : G) :
    (μ.map (X + Z)).real {x} = ∑ s, (μ.map Z).real {s} * (μ.map X).real {x - s} := by
  rw [measureReal_def, h_indep.map_add_singleton_eq_sum hX hZ, ENNReal.toReal_sum]
  · congr with a
    rw [ENNReal.toReal_mul]
    rfl
  · intro a ha
    finiteness

lemma absolutelyContinuous_add_of_indep [Finite G] [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X Y Z : Ω → G} (h_indep : IndepFun (⟨X, Y⟩) Z μ) (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z)
    (habs : ∀ x, μ.map Y {x} = 0 → μ.map X {x} = 0) :
    ∀ x, μ.map (Y + Z) {x} = 0 → μ.map (X + Z) {x} = 0 := by
  cases nonempty_fintype G
  intro x hx
  have IX : IndepFun X Z μ := h_indep.comp (φ := Prod.fst) (ψ := id) measurable_fst measurable_id
  have IY : IndepFun Y Z μ := h_indep.comp (φ := Prod.snd) (ψ := id) measurable_snd measurable_id
  rw [IY.map_add_singleton_eq_sum hY hZ, Finset.sum_eq_zero_iff] at hx
  rw [IX.map_add_singleton_eq_sum hX hZ, Finset.sum_eq_zero_iff]
  intro i hi
  rcases mul_eq_zero.1 (hx i hi) with h'i | h'i
  · simp [h'i]
  · simp [habs _ h'i]

/-- If $X, Y, Z$ are independent $G$-valued random variables, then
  $$D_{KL}(X+Z\Vert Y+Z) \leq D_{KL}(X\Vert Y).$$ -/
lemma KLDiv_add_le_KLDiv_of_indep [Finite G] [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X Y Z : Ω → G} [IsZeroOrProbabilityMeasure μ]
    (h_indep : IndepFun (⟨X, Y⟩) Z μ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (habs : ∀ x, μ.map Y {x} = 0 → μ.map X {x} = 0) :
    KL[X + Z ; μ # Y + Z ; μ] ≤ KL[X ; μ # Y ; μ] := by
  cases nonempty_fintype G
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [KLDiv]
  set X' : G → Ω → G := fun s ↦ (· + s) ∘ X with hX'
  set Y' : G → Ω → G := fun s ↦ (· + s) ∘ Y with hY'
  have AX' x i : (μ.map (X' i)).real {x} = (μ.map X).real {x - i} := by
    rw [measureReal_def, measureReal_def, hX', ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
    congr!
    ext y
    simp [sub_eq_add_neg]
  have AY' x i : (μ.map (Y' i)).real {x} = (μ.map Y).real {x - i} := by
    rw [measureReal_def, measureReal_def, hY', ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
    congr!
    ext y
    simp [sub_eq_add_neg]
  let w (s : G) : ℝ := (μ.map Z).real {s}
  have sum_w : ∑ s, w s = 1 := by
    have : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
    simp [w]
  have A x : (μ.map (X + Z)).real {x} = ∑ s, w s * (μ.map (X' s)).real {x} := by
    have : IndepFun X Z μ := h_indep.comp (φ := Prod.fst) (ψ := id) measurable_fst measurable_id
    rw [this.real_map_add_singleton_eq_sum hX hZ]
    congr with i
    congr 1
    rw [AX']
  have B x : (μ.map (Y + Z)).real {x} = ∑ s, w s * (μ.map (Y' s)).real {x} := by
    have : IndepFun Y Z μ := h_indep.comp (φ := Prod.snd) (ψ := id) measurable_snd measurable_id
    rw [this.real_map_add_singleton_eq_sum hY hZ]
    congr with i
    congr 1
    rw [AY']
  have : KL[X + Z ; μ # Y + Z; μ] ≤ ∑ s, w s * KL[X' s ; μ # Y' s ; μ] := by
    apply KLDiv_of_convex (fun s _ ↦ by simp [w])
    · exact A
    · exact B
    · intro s _ x
      simpa [AX', AY', measureReal_eq_zero_iff] using habs _
  apply this.trans_eq
  have C s : KL[X' s ; μ # Y' s ; μ] = KL[X ; μ # Y ; μ] :=
    KLDiv_of_comp_inj (add_left_injective s) hX hY
  simp_rw [C, ← Finset.sum_mul, sum_w, one_mul]

/-- If $X,Y,Z$ are random variables, with $X,Z$ defined on the same sample space, we define
$$ D_{KL}(X|Z \Vert Y) := \sum_z \mathbf{P}(Z=z) D_{KL}( (X|Z=z) \Vert Y).$$ -/
noncomputable def condKLDiv {S : Type*} (X : Ω → G) (Y : Ω' → G) (Z : Ω → S)
    (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) : ℝ :=
  ∑' z, μ.real (Z⁻¹' {z}) * KL[X ; cond μ (Z⁻¹' {z}) # Y ; μ']

@[inherit_doc condKLDiv]
notation3:max "KL[" X " | " Z " ; " μ " # " Y " ; " μ' "]" => condKLDiv X Y Z μ μ'

@[inherit_doc condKLDiv]
notation3:max "KL[" X " | " Z " # " Y "]" => condKLDiv X Y Z volume volume

/-- If $X, Y$ are $G$-valued random variables, and $Z$ is another random variable
  defined on the same sample space as $X$, then
  $$D_{KL}((X|Z)\Vert Y) = D_{KL}(X\Vert Y) + \bbH[X] - \bbH[X|Z].$$ -/
lemma condKLDiv_eq {S : Type*} [MeasurableSpace S] [Finite S] [MeasurableSingletonClass S]
    [Finite G] [IsZeroOrProbabilityMeasure μ] [IsFiniteMeasure μ']
    {X : Ω → G} {Y : Ω' → G} {Z : Ω → S}
    (hX : Measurable X) (hZ : Measurable Z)
    (habs : ∀ x, μ'.map Y {x} = 0 → μ.map X {x} = 0) :
    KL[ X | Z ; μ # Y ; μ'] = KL[X ; μ # Y ; μ'] + H[X ; μ] - H[ X | Z ; μ] := by
  cases nonempty_fintype G
  cases nonempty_fintype S
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condKLDiv, tsum_fintype, KLDiv_eq_sum, Finset.mul_sum, entropy_eq_sum]
  simp only [condKLDiv, tsum_fintype, KLDiv_eq_sum, Finset.mul_sum, entropy_eq_sum]
  rw [Finset.sum_comm, condEntropy_eq_sum_sum_fintype hZ, Finset.sum_comm (α := G),
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  congr with g
  simp only [negMulLog, neg_mul, Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add, ← sub_eq_add_neg,
    ← mul_sub]
  simp_rw [← map_measureReal_apply hZ (measurableSet_singleton _)]
  have A : Measure.map X μ {g} = ∑ x, μ.map Z {x} * (Measure.map X μ[|Z ⁻¹' {x}] {g}) := by
    simp_rw [Measure.map_apply hZ (measurableSet_singleton _)]
    have : Measure.map X μ {g} = Measure.map X (∑ x, μ (Z ⁻¹' {x}) • μ[|Z ⁻¹' {x}]) {g} := by
      rw [sum_meas_smul_cond_fiber hZ μ]
    rw [← MeasureTheory.Measure.sum_fintype, Measure.map_sum hX.aemeasurable] at this
    simpa using this
  have : (Measure.map X μ).real {g} =
      ∑ x, (Measure.map Z μ).real {x} * (Measure.map X μ[|Z ⁻¹' {x}]).real {g} := by
    rw [measureReal_def, A, ENNReal.toReal_sum (fun a ha ↦ by finiteness)]
    congr with x
    rw [ENNReal.toReal_mul]
    rfl
  nth_rewrite 1 [this]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  congr with s
  rw [mul_assoc, ← mul_add, ← mul_add]
  rcases eq_or_ne ((Measure.map Z μ).real {s}) 0 with hs | hs
  · simp [hs]
  rcases eq_or_ne ((Measure.map X μ[|Z ⁻¹' {s}]).real {g}) 0 with hg | hg
  · simp [hg]
  congr
  have hXg : (μ.map X).real {g} ≠ 0 := by
    intro h
    rw [this, Finset.sum_eq_zero_iff_of_nonneg (fun a ha ↦ by positivity)] at h
    specialize h s (Finset.mem_univ _)
    rw [mul_eq_zero] at h
    tauto
  have hYg : μ'.map Y {g} ≠ 0 := fun h ↦ by simp [measureReal_def, habs _ h] at hXg
  have hYg' : (μ'.map Y).real {g} ≠ 0 := by simp [measureReal_eq_zero_iff, hYg]
  rw [Real.log_div hg hYg', Real.log_div hXg hYg']
  abel

/-- `KL(X|Z ‖ Y) ≥ 0`. -/
lemma condKLDiv_nonneg {S : Type*} [MeasurableSingletonClass G] [Finite G]
    {X : Ω → G} {Y : Ω' → G} {Z : Ω → S}
    [IsZeroOrProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, μ'.map Y {x} = 0 → μ.map X {x} = 0) :
    0 ≤ KL[X | Z; μ # Y ; μ'] := by
  rw [condKLDiv]
  refine tsum_nonneg (fun i ↦ mul_nonneg (by simp) ?_)
  apply KLDiv_nonneg hX hY
  intro s hs
  specialize habs s hs
  rw [Measure.map_apply hX (measurableSet_singleton s)] at habs ⊢
  exact cond_absolutelyContinuous habs

lemma tendsto_KLDiv_id_right [TopologicalSpace G] [DiscreteTopology G] [Finite G]
    [DiscreteMeasurableSpace G] [IsFiniteMeasure μ]
    {α : Type*} {l : Filter α} {ν : α → ProbabilityMeasure G} {ν' : ProbabilityMeasure G}
    (h : Tendsto ν l (𝓝 ν')) (habs : ∀ x, ν' {x} = 0 → μ.map X {x} = 0) :
    Tendsto (fun n ↦ KL[X ; μ # id ; ν n]) l (𝓝 (KL[X ; μ # id ; ν'])) := by
  cases nonempty_fintype G
  simp_rw [KLDiv_eq_sum]
  apply tendsto_finset_sum _ (fun g hg ↦ ?_)
  rcases eq_or_ne ((Measure.map X μ).real {g}) 0 with h'g | h'g
  · simpa [h'g] using tendsto_const_nhds
  apply Tendsto.mul tendsto_const_nhds
  have νg : (ν' : Measure G).real {g} ≠ 0 := by
    intro h
    rw [measureReal_eq_zero_iff] at h
    apply h'g
    rw [measureReal_eq_zero_iff]
    apply habs
    exact (ν'.null_iff_toMeasure_null {g}).mpr h
  apply Tendsto.log; swap
  · simp only [Measure.map_id, ne_eq, div_eq_zero_iff, h'g, false_or, νg, not_false_eq_true]
  apply Tendsto.div tendsto_const_nhds _ (by simpa using νg)
  simp only [Measure.map_id]
  simp only [measureReal_def]
  rw [ENNReal.tendsto_toReal_iff (by simp) (by simp)]
  exact (ProbabilityMeasure.tendsto_iff_forall_apply_tendsto_ennreal _ _).1 h g

lemma tendsto_KLDiv_id_left [TopologicalSpace G] [DiscreteTopology G] [Finite G]
    [DiscreteMeasurableSpace G] {Y : Ω → G} {μ : Measure Ω}
    {α : Type*} {l : Filter α} {ν : α → ProbabilityMeasure G} {ν' : ProbabilityMeasure G}
    (h : Tendsto ν l (𝓝 ν')) :
    Tendsto (fun n ↦ KL[id ; ν n # Y ; μ]) l (𝓝 (KL[id ; ν' # Y ; μ])) := by
  cases nonempty_fintype G
  simp_rw [KLDiv_eq_sum_negMulLog]
  apply tendsto_finset_sum _ (fun g hg ↦ ?_)
  apply Tendsto.const_mul
  apply continuous_negMulLog.continuousAt.tendsto.comp
  apply Tendsto.div_const
  simp only [Measure.map_id, measureReal_def]
  rw [ENNReal.tendsto_toReal_iff (by simp) (by simp)]
  exact (ProbabilityMeasure.tendsto_iff_forall_apply_tendsto_ennreal _ _).1 h g
