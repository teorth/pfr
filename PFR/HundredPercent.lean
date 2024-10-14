import PFR.ForMathlib.Entropy.RuzsaDist

/-!
# The 100% version of entropic PFR

Here we show entropic PFR in the case of doubling constant zero.

## Main results

* `exists_isUniform_of_rdist_eq_zero` : If $d[X_1;X_2]=0$, then there exists a subgroup $H \leq G$ such that $d[X_1;U_H] = d[X_2;U_H] = 0$.
-/

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} {G : Type*} [MeasureSpace Ω] [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] {X : Ω → G}

/-- The symmetry group Sym of $X$: the set of all $h ∈ G$ such that $X + h$ has an identical
distribution to $X$. -/
def symmGroup (X : Ω → G) (hX : Measurable X) : AddSubgroup G where
  carrier := {x | IdentDistrib X (fun ω ↦ X ω + x)}
  add_mem' := by
    intro x y hx hy
    let f : G → G := fun g ↦ g + x
    have : IdentDistrib (f ∘ X) (fun ω ↦ f (X ω + y)) := hy.comp $ measurable_add_const _
    have Z := hx.trans this
    dsimp
    convert Z using 1
    ext ω
    simp only [f]
    abel
  zero_mem' := by simpa using IdentDistrib.refl hX.aemeasurable
  neg_mem' := by
    intro x hx
    dsimp at hx ⊢
    let f : G → G := fun g ↦ g - x
    have : IdentDistrib (f ∘ X) (fun ω ↦ f (X ω + x)) := hx.comp $ measurable_sub_const' _
    convert this.symm using 1
    · ext ω
      simp only [f]
      abel
    · ext ω
      simp only [Function.comp_apply]
      abel_nf

@[simp] lemma mem_symmGroup (hX : Measurable X) {x : G} :
    x ∈ symmGroup X hX ↔ IdentDistrib X (fun ω ↦ X ω + x) := Iff.rfl

lemma ProbabilityTheory.IdentDistrib.symmGroup_eq {Ω' : Type*} [MeasureSpace Ω'] {X' : Ω' → G}
    (hX : Measurable X) (hX' : Measurable X') (h : IdentDistrib X X') :
    symmGroup X hX = symmGroup X' hX' := by
  ext x
  have A : Measurable (fun a ↦ a + x) := measurable_add_const _
  exact ⟨fun H ↦ h.symm.trans (H.trans (h.comp A)), fun H ↦ h.trans (H.trans (h.symm.comp A))⟩

variable [Fintype G] [MeasurableSingletonClass G] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- If $d[X ;X]=0$, and $x,y \in G$ are such that $P[X=x], P[X=y]>0$,
then $x-y \in \mathrm{Sym}[X]$. -/
lemma sub_mem_symmGroup (hX : Measurable X) (hdist : d[X # X] = 0)
    {x y : G} (hx : ℙ (X⁻¹' {x}) ≠ 0) (hy : ℙ (X⁻¹' {y}) ≠ 0) : x - y ∈ symmGroup X hX := by
  /- Consider two independent copies `X'` and `Y'` of `X`. The assumption on the Rusza distance
  ensures that `H[X' - Y' | Y'] = H[X' - Y']`, i.e., `X' - Y'` and `Y'` are independent. Therefore,
  the distribution of `X' - c` is independent of `c` for `c` in the support of `Y'`.
  In particular, `X' - x` and `X' - y` have the same distribution, which is equivalent to the
  claim of the lemma. -/
  rcases ProbabilityTheory.independent_copies_two hX hX with
    ⟨Ω', mΩ', X', Y', hP, hX', hY', hindep, hidX, hidY⟩
  rw [hidX.symm.symmGroup_eq hX hX']
  have A : H[X' - Y' | Y'] = H[X' - Y'] := calc
    H[X' - Y' | Y'] = H[X' | Y'] := condEntropy_sub_right hX' hY'
    _ = H[X'] := hindep.condEntropy_eq_entropy hX' hY'
    _ = H[X' - Y'] := by
      have : d[X' # Y'] = 0 := by rwa [hidX.rdist_eq hidY]
      rw [hindep.rdist_eq hX' hY', ← (hidX.trans hidY.symm).entropy_eq] at this
      linarith
  have I : IndepFun (X' - Y') Y' := by
    refine (mutualInfo_eq_zero (by fun_prop) hY').1 ?_
    rw [mutualInfo_eq_entropy_sub_condEntropy (by fun_prop) hY', A, sub_self]
  have M : ∀ c, ℙ (Y' ⁻¹' {c}) ≠ 0 → IdentDistrib (fun ω ↦ X' ω - c) (X' - Y') := by
    intro c hc
    let F := fun ω ↦ X' ω - c
    refine ⟨by fun_prop, by fun_prop, ?_⟩
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs, Measure.map_apply (by fun_prop) hs]
    have : ℙ (F ⁻¹' s) * ℙ (Y' ⁻¹' {c}) = ℙ ((X' - Y') ⁻¹' s) * ℙ (Y' ⁻¹' {c}) := by calc
      ℙ (F ⁻¹' s) * ℙ (Y' ⁻¹' {c}) = ℙ (F ⁻¹' s ∩ Y' ⁻¹' {c}) := by
        have hFY' : IndepFun F Y' := by
          have : Measurable (fun z ↦ z - c) := measurable_sub_const' c
          apply hindep.comp this measurable_id
        rw [indepFun_iff_measure_inter_preimage_eq_mul.1 hFY' _ _ hs .of_discrete]
      _ = ℙ ((X' - Y') ⁻¹' s ∩ Y' ⁻¹' {c}) := by
        congr 1; ext z; simp (config := {contextual := true})
      _ = ℙ ((X' - Y') ⁻¹' s) * ℙ (Y' ⁻¹' {c}) := by
        rw [indepFun_iff_measure_inter_preimage_eq_mul.1 I _ _ hs $ .of_discrete]
    rwa [ENNReal.mul_eq_mul_right hc (measure_ne_top ℙ _)] at this
  have J : IdentDistrib (fun ω ↦ X' ω - x) (fun ω ↦ X' ω - y) := by
    have Px : ℙ (Y' ⁻¹' {x}) ≠ 0 := by
      convert hx; exact hidY.measure_mem_eq $ .of_discrete
    have Py : ℙ (Y' ⁻¹' {y}) ≠ 0 := by
      convert hy; exact hidY.measure_mem_eq $ .of_discrete
    exact (M x Px).trans (M y Py).symm
  have : IdentDistrib X' (fun ω ↦ X' ω + (x - y)) := by
    have : Measurable (fun c ↦ c + x) := measurable_add_const x
    convert J.comp this using 1
    · ext ω; simp
    · ext ω; simp; abel
  exact this

/-- If `d[X # X] = 0`, then `X - x₀` is the uniform distribution on the subgroup of `G`
stabilizing the distribution of `X`, for any `x₀` of positive probability. -/
lemma isUniform_sub_const_of_rdist_eq_zero (hX : Measurable X) (hdist : d[X # X] = 0) {x₀ : G}
    (hx₀ : ℙ (X⁻¹' {x₀}) ≠ 0) : IsUniform (symmGroup X hX) (fun ω ↦ X ω - x₀) where
  eq_of_mem := by
    have B c z : (fun ω ↦ X ω - c) ⁻¹' {z} = X ⁻¹' {c + z} := by
      ext w; simp [sub_eq_iff_eq_add']
    have A : ∀ (z : G), z ∈ symmGroup X hX →
        ℙ ((fun ω ↦ X ω - x₀) ⁻¹' {z}) = ℙ ((fun ω ↦ X ω - x₀) ⁻¹' {0}) := by
      intro z hz
      have : X ⁻¹' {x₀ + z} = (fun ω ↦ X ω - z) ⁻¹' {x₀} := by simp [B, add_comm]
      simp_rw [B, add_zero, this]
      have Z := (mem_symmGroup hX).1 (AddSubgroup.neg_mem (symmGroup X hX) hz)
      simp [← sub_eq_add_neg] at Z
      exact Z.symm.measure_mem_eq $ .of_discrete
    intro x y hx hy
    rw [A x hx, A y hy]
  measure_preimage_compl := by
    apply (measure_preimage_eq_zero_iff_of_countable (Set.to_countable _)).2
    intro x hx
    contrapose! hx
    have B : (fun ω ↦ X ω - x₀) ⁻¹' {x} = X ⁻¹' {x₀ + x} := by
      ext w; simp [sub_eq_iff_eq_add']
    rw [B] at hx
    simpa using sub_mem_symmGroup hX hdist hx hx₀

/-- If $d[X ;X]=0$, then there exists a subgroup $H \leq G$ such that $d[X ;U_H] = 0$. -/
theorem exists_isUniform_of_rdist_self_eq_zero (hX : Measurable X) (hdist : d[X # X] = 0) :
    ∃ H : AddSubgroup G, ∃ U : Ω → G, Measurable U ∧ IsUniform H U ∧ d[X # U] = 0 := by
  -- use for `U` a translate of `X` to make sure that `0` is in its support.
  obtain ⟨x₀, h₀⟩ : ∃ x₀, ℙ (X⁻¹' {x₀}) ≠ 0 := by
    by_contra! h
    have A a : (ℙ : Measure Ω).map X {a} = 0 := by
      rw [Measure.map_apply hX $ .of_discrete]
      exact h _
    have B : (ℙ : Measure Ω).map X = 0 := by
      rw [← Measure.sum_smul_dirac (μ := (ℙ : Measure Ω).map X)]
      simp [A]
    have : IsProbabilityMeasure ((ℙ : Measure Ω).map X) :=
      isProbabilityMeasure_map hX.aemeasurable
    exact IsProbabilityMeasure.ne_zero _ B
  refine ⟨symmGroup X hX, fun ω ↦ X ω - x₀, hX.sub_const _,
    isUniform_sub_const_of_rdist_eq_zero hX hdist h₀, ?_⟩
  simp_rw [sub_eq_add_neg]
  suffices d[X # X + fun _ ↦ -x₀] = 0 by convert this
  rw [rdist_add_const hX hX]
  exact hdist

/-- If $d[X_1;X_2]=0$, then there exists a subgroup $H \leq G$ such that
$d[X_1;U_H] = d[X_2;U_H] = 0$. Follows from the preceding claim by the triangle inequality. -/
theorem exists_isUniform_of_rdist_eq_zero
    {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')] {X' : Ω' → G}
    (hX : Measurable X) (hX' : Measurable X') (hdist : d[X # X'] = 0) :
    ∃ H : AddSubgroup G, ∃ U : Ω → G,
      Measurable U ∧ IsUniform H U ∧ d[X # U] = 0 ∧ d[X' # U] = 0 := by
  have h' : d[X # X] = 0 := by
    apply le_antisymm _ (rdist_nonneg hX hX)
    calc
      d[X # X] ≤ d[X # X'] + d[X' # X] := rdist_triangle hX hX' hX
      _ = 0 := by rw [hdist, rdist_symm, hdist, zero_add]
  rcases exists_isUniform_of_rdist_self_eq_zero hX h' with ⟨H, U, hmeas, hunif, hd⟩
  refine ⟨H, U, hmeas, hunif, hd, ?_⟩
  apply le_antisymm _ (rdist_nonneg hX' hmeas)
  calc
    d[X' # U] ≤ d[X' # X] + d[X # U] := rdist_triangle hX' hX hmeas
    _ = 0 := by rw [hd, rdist_symm, hdist, zero_add]
