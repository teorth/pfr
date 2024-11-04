import PFR.ForMathlib.CompactProb
import PFR.ForMathlib.Entropy.RuzsaDist
import PFR.Kullback
import Mathlib.MeasureTheory.Measure.AEMeasurable


/-!
# The rho functional

Definition of the rho functional and basic facts

## Main definitions:

## Main results

-/


/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))


open MeasureTheory ProbabilityTheory Real
open scoped Pointwise ENNReal
universe uG

variable {G : Type uG} [AddCommGroup G] [Fintype G] [hGm : MeasurableSpace G]
[DiscreteMeasurableSpace G]

/-- The set of possible values of $D_{KL}(X \Vert U_A + T)$, where $U_A$ is uniform on $A$ and
$T$ ranges over $G$-valued random variables independent of $U_A$. We also require an absolute
continuity condition so that the KL divergence makes sense in `ℝ`.

To avoid universe issues, we express this using measures on `G`, but the equivalence with the
above point of view follows from `rhoMinus_le` below. -/
noncomputable def rhoMinusSet {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : Set ℝ :=
  {x : ℝ | ∃ (μ : Measure G), IsProbabilityMeasure μ ∧
    (∀ y, (μ.prod (uniformOn A)).map (Prod.fst + Prod.snd) {y} = 0 → volume.map X {y} = 0) ∧
    x = KL[X ; ℙ # Prod.fst + Prod.snd ; μ.prod (uniformOn A)]}

lemma nonempty_rhoMinusSet {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → G) (A : Finset G)  (hX : Measurable X) (hA : A.Nonempty) :
    Set.Nonempty (rhoMinusSet X A) := by
  obtain ⟨a, ha⟩ : ∃ x, x ∈ A := by exact hA
  set μ := volume.map ((· - a) ∘ X) with hμ
  set ν := uniformOn (A : Set G) with hν
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have : IsProbabilityMeasure ν :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
  refine ⟨_, ⟨μ, by infer_instance, fun y h ↦ ?_, rfl⟩⟩
  have h_indep : IndepFun Prod.fst Prod.snd (μ.prod ν) := ProbabilityTheory.indepFun_fst_snd
  rw [← hν, h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp)] at h
  specialize h a (Finset.mem_univ a)
  have : (Measure.map Prod.snd (μ.prod ν)) {a} ≠ 0 := by
    simp [Measure.map_snd_prod, ν, uniformOn_apply_singleton_of_mem (by exact ha) A.finite_toSet]
  simp only [mul_eq_zero, this, false_or, Measure.map_fst_prod] at h
  simp only [measure_univ, one_smul] at h
  rw [hμ, ← Measure.map_map (by fun_prop) hX,
    Measure.map_apply (by fun_prop) (measurableSet_singleton (y - a))] at h
  convert h
  ext z
  simp

lemma nonneg_of_mem_rhoMinusSet {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → G) (A : Finset G)
    (hX : Measurable X) {x : ℝ} (hx : x ∈ rhoMinusSet X A) : 0 ≤ x := by
  rcases hx with ⟨μ, hμ, habs, rfl⟩
  exact KLDiv_nonneg hX (by fun_prop) habs

lemma bddBelow_rhoMinusSet {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → G) (A : Finset G) (hX : Measurable X) :
    BddBelow (rhoMinusSet X A) :=
  ⟨0, fun _ hx ↦ nonneg_of_mem_rhoMinusSet X A hX hx⟩


/-- For any $G$-valued random variable $X$, we define $\rho^-(X)$ to be the infimum of
$D_{KL}(X \Vert U_A + T)$, where $U_A$ is uniform on $A$ and $T$ ranges over $G$-valued random
variables independent of $U_A$. -/
noncomputable def rhoMinus {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ :=
  sInf (rhoMinusSet X A)

lemma rhoMinus_le {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (X : Ω → G) (A : Finset G)  (hX : Measurable X) (hA : A.Nonempty)
    {Ω' : Type*} [MeasureSpace Ω'] (T : Ω' → G) (U : Ω' → G)
    [IsProbabilityMeasure (ℙ : Measure Ω')] (hunif : IsUniform A U) (hT : Measurable T)
    (hU : Measurable U) (hindep : IndepFun T U)
    (habs : ∀ y, (volume.map (T + U)) {y} = 0 → volume.map X {y} = 0) :
    rhoMinus X A ≤ KL[X # T + U] := by
  have : IsProbabilityMeasure (Measure.map T ℙ) := isProbabilityMeasure_map hT.aemeasurable
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
  have E : Measure.map U ℙ = uniformOn (A : Set G) := hunif.map_eq_uniformOn hU A.finite_toSet hA
  have M : (Measure.map (Prod.fst + Prod.snd) ((Measure.map T ℙ).prod (uniformOn ↑A))) =
      (Measure.map (T + U) ℙ) := by
    ext s _
    rw [hindep.map_add_eq_sum hT hU]
    have : IndepFun Prod.fst Prod.snd ((Measure.map T ℙ).prod (uniformOn (A : Set G))) :=
      ProbabilityTheory.indepFun_fst_snd
    rw [this.map_add_eq_sum measurable_fst measurable_snd,
      Measure.map_fst_prod, Measure.map_snd_prod]
    simp [E]
  apply csInf_le (bddBelow_rhoMinusSet X A hX)
  simp only [rhoMinusSet, Set.mem_setOf_eq]
  exact ⟨volume.map T, isProbabilityMeasure_map hT.aemeasurable, by rwa [M], by simp [KLDiv, M]⟩

/-- For any $G$-valued random variable $X$, we define $\rho^+(X) := \rho^-(X) + \bbH(X) - \bbH(U_A)$. -/
noncomputable def rhoPlus {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ := (rhoMinus X A) + H[ X ] - log (Nat.card A)

/-- We have $\rho^-(X) \geq 0$. -/
lemma rhoMinus_nonneg {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : Ω → G} (A : Finset G) (hX : Measurable X) : 0 ≤ rhoMinus X A :=
  Real.sInf_nonneg (fun _ hx ↦ nonneg_of_mem_rhoMinusSet X A hX hx)

open Set

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

private lemma le_rhoMinus_of_subgroup (H : AddSubgroup G) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (U : Ω → G) (hunif : IsUniform H U) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    log (Nat.card A) -
      log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) ≤ rhoMinus U A := by
  apply le_csInf (nonempty_rhoMinusSet U A hU hA)
  rintro - ⟨μ, hμ, habs, rfl⟩
  let T : G × G → G := Prod.fst
  have hT : Measurable T := measurable_fst
  let UA : G × G → G := Prod.snd
  have hUA : Measurable UA := measurable_snd
  letI : MeasureSpace (G × G) := ⟨μ.prod (uniformOn (A : Set G))⟩
  have hprod : (ℙ : Measure (G × G)) = μ.prod (uniformOn (A : Set G)) := rfl
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
  have : IsProbabilityMeasure (Measure.map T ℙ) := by rw [hprod, Measure.map_fst_prod]; simp [hμ]
  have h_indep : IndepFun T UA := ProbabilityTheory.indepFun_fst_snd
  have hUA_unif : IsUniform A UA := by
    have : IsUniform A id (uniformOn (A : Set G)) := isUniform_uniformOn
    apply IsUniform.of_identDistrib this ?_ A.measurableSet
    exact measurePreserving_snd.identDistrib aemeasurable_id
  have : IsProbabilityMeasure (ℙ : Measure (G × G)) := by rw [hprod]; infer_instance
  let H' : Finset G := Set.Finite.toFinset (toFinite H)
  have hunif' : IsUniform H' U := by convert hunif; simp [H']
  have I₁ : KL[U # T + UA] =
      ∑ h ∈ H', 1/Nat.card H * log ((1/Nat.card H) / (volume.map (T + UA) {h}).toReal) := by
    rw [KLDiv_eq_sum, ← Finset.sum_subset (Finset.subset_univ H')]; swap
    · intro x _ hH
      rw [Measure.map_apply hU (measurableSet_singleton x), hunif.measure_preimage_of_nmem]
      · simp
      · simpa [H'] using hH
    apply Finset.sum_congr rfl (fun i hi ↦ ?_)
    rw [← measureReal_def, hunif'.measureReal_preimage_of_mem' hU hi]
    congr <;> simp [H']
  have I₂ : (∑ h ∈ H', 1/Nat.card H : ℝ) * log ((∑ h ∈ H', 1/Nat.card H : ℝ)
      / (∑ h ∈ H', (volume.map (T + UA) {h}).toReal)) ≤ KL[U # T + UA] := by
    rw [I₁]
    apply Real.sum_mul_log_div_leq (by simp) (by simp) (fun i hi h'i ↦ ?_)
    simp [ENNReal.toReal_eq_zero_iff] at h'i
    have : (Measure.map U ℙ {i}).toReal = 0 := by simp [habs i h'i]
    rw [← measureReal_def, hunif'.measureReal_preimage_of_mem' hU hi] at this
    simpa [H'] using this
  have : (∑ h ∈ H', 1/Nat.card H : ℝ) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_one]
    rw [div_eq_one_iff_eq]
    · simp [H', ← Nat.card_eq_card_finite_toFinset]
    · simp [ne_of_gt]
  simp only [this, one_mul] at I₂
  simp only [Finset.sum_toReal_measure_singleton, one_div, log_inv] at I₂
  apply le_trans _ I₂
  have I₃ : ((Measure.map (T + UA) ℙ) ↑H').toReal
      ≤ 1 * ((sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G}) / Nat.card A) := by
    have : ∑ x : G, ((Measure.map T ℙ) {x}).toReal = 1 := by simp
    rw [← this, add_comm, h_indep.symm.map_add_eq_sum hUA hT,
      ENNReal.toReal_sum (by simp [ENNReal.mul_eq_top]), Finset.sum_mul]
    simp_rw [ENNReal.toReal_mul,
      Measure.map_apply hUA (DiscreteMeasurableSpace.forall_measurableSet _),
      hUA_unif.measure_preimage hUA]
    simp only [measure_univ, singleton_add, image_add_left, neg_neg, one_mul,
      Nat.card_eq_fintype_card, Fintype.card_coe, ENNReal.toReal_div, ENNReal.toReal_nat]
    apply Finset.sum_le_sum (fun i _ ↦ ?_)
    gcongr
    apply le_csSup bddAbove_card_inter_add
    rw [inter_comm]
    refine ⟨-i, ?_⟩
    congr
    ext j
    simp [H', mem_vadd_set_iff_neg_vadd_mem]
  rw [one_mul] at I₃
  have : - log ((sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G}) / Nat.card A) ≤
      - log ((Measure.map (T + UA) ℙ) ↑H').toReal := by
    apply neg_le_neg
    apply log_le_log _ I₃
    apply lt_of_le_of_ne (by simp) (fun h ↦ ?_)
    rw [Eq.comm, ENNReal.toReal_eq_zero_iff] at h
    simp only [measure_ne_top, or_false] at h
    have : Measure.map (T + UA) ℙ ({(0 : G)} : Set G) = 0 :=
      measure_mono_null (by simp [H', AddSubgroup.zero_mem]) h
    have Z := habs _ this
    rw [Measure.map_apply hU (measurableSet_singleton 0),
      hunif'.measure_preimage_of_mem hU (by simp [H', AddSubgroup.zero_mem])] at Z
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

private lemma rhoMinus_le_of_subgroup {H : AddSubgroup G} {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (t : G)
    (U : Ω → G) (hunif : IsUniform H U) {A : Finset G} (hA : A.Nonempty)
    (h'A : (A ∩ (t +ᵥ (H : Set G)) : Set G).Nonempty)
    (hU : Measurable U) :
    rhoMinus U A ≤ log (Nat.card A) -
      log (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)) := by
  have mapU : Measure.map U ℙ = uniformOn (H : Set G) :=
    hunif.map_eq_uniformOn hU (toFinite H) H.coe_nonempty
  obtain ⟨a, ha, h'a⟩ := by exact h'A
  rcases mem_vadd_set.1 h'a with ⟨v, vH, rfl⟩
  simp only [vadd_eq_add, Finset.mem_coe] at ha
  have P z : (fun x ↦ x - t) ⁻¹' {z} = {z + t} := by ext w; simp [sub_eq_iff_eq_add]
  set μ := volume.map ((· - t) ∘ U) with hμ
  have μ_sing z : μ {z} = uniformOn (H : Set G) {z + t} := by
    rw [hμ, ← Measure.map_map (by fun_prop) hU,
      Measure.map_apply (by fun_prop) (measurableSet_singleton _), mapU, P]
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
  have : IsProbabilityMeasure μ :=
    isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have h_indep : IndepFun Prod.fst Prod.snd (μ.prod (uniformOn (A : Set G))) := indepFun_fst_snd
  apply csInf_le (bddBelow_rhoMinusSet U A hU)
  simp only [rhoMinusSet, Nat.card_eq_fintype_card, Fintype.card_coe, mem_setOf_eq]
  refine ⟨μ, this, fun y h ↦ ?_, ?_⟩
  · rw [mapU]
    apply uniformOn_apply_singleton_of_nmem (fun yH ↦ ?_)
    rw [h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd,
      Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp), Measure.map_snd_prod,
      Measure.map_fst_prod] at h
    specialize h (t + v)
    simp only [Finset.mem_univ, measure_univ, one_smul,
      uniformOn_apply_singleton_of_mem (by exact ha) A.finite_toSet, Finset.coe_sort_coe,
      Nat.card_eq_fintype_card, Fintype.card_coe, one_div, μ_sing, mul_eq_zero, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, false_or, true_implies] at h
    rw [uniformOn_apply_singleton_of_mem _ (toFinite (H : Set G))] at h
    · simp at h
    · convert (H.sub_mem yH vH) using 1
      abel
  let H' : Finset G := Set.Finite.toFinset (toFinite H)
  have hunif' : IsUniform H' U := by convert hunif; simp [H']
  rw [KLDiv_eq_sum, ← Finset.sum_subset (Finset.subset_univ H')]; swap
  · intro x _ hH
    rw [Measure.map_apply hU (measurableSet_singleton x), hunif.measure_preimage_of_nmem]
    · simp
    · simpa [H'] using hH
  have : ∑ x ∈ H', ((Measure.map U ℙ) {x}).toReal *
      log (((Measure.map U ℙ) {x}).toReal
        / ((Measure.map (Prod.fst + Prod.snd) (μ.prod (uniformOn ↑A))) {x}).toReal)
      = ∑ x ∈ H', (1/Nat.card H) * log ((1/Nat.card H)
        / (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) / (Nat.card A * Nat.card H))) := by
    apply Finset.sum_congr rfl (fun x hx ↦ ?_)
    have xH : x ∈ H := by simpa [H'] using hx
    have : (Measure.map U ℙ) {x} = 1/Nat.card H := by
      rw [Measure.map_apply hU (measurableSet_singleton _), hunif'.measure_preimage_of_mem hU hx]
      simp [H']
    simp only [this, one_div, ENNReal.toReal_inv, ENNReal.toReal_nat, Nat.cast_eq_zero]
    congr
    rw [h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd, Measure.map_snd_prod,
      Measure.map_fst_prod]
    simp only [measure_univ, one_smul, μ_sing]
    let F : Finset G := Set.Finite.toFinset (toFinite (A ∩ (t +ᵥ (H : Set G)) : Set G))
    rw [← Finset.sum_subset (Finset.subset_univ F)]; swap
    · intro i _ hi
      simp only [Finite.mem_toFinset, mem_inter_iff, Finset.mem_coe, not_and, F] at hi
      simp only [mul_eq_zero]
      by_cases h'i : i ∈ A
      · right
        apply uniformOn_apply_singleton_of_nmem (fun h'x ↦ ?_)
        apply hi h'i
        exact ⟨x - (x-i+t), H.sub_mem xH h'x, by simp; abel⟩
      · left
        exact uniformOn_apply_singleton_of_nmem h'i
    have : ∑ i ∈ F, (uniformOn ↑A) {i} * (uniformOn ↑H) {x - i + t} =
        ∑ i ∈ F, (1 / Nat.card A * (1 / Nat.card H) : ℝ≥0∞) := by
      apply Finset.sum_congr rfl (fun i hi ↦ ?_)
      simp only [Finite.mem_toFinset, mem_inter_iff, Finset.mem_coe, F] at hi
      rw [uniformOn_apply_singleton_of_mem (by exact hi.1) A.finite_toSet]
      rw [uniformOn_apply_singleton_of_mem _ (toFinite _)]; swap
      · convert H.sub_mem xH (mem_vadd_set_iff_neg_vadd_mem.1 hi.2) using 1
        simp
        abel
      rfl
    simp only [this, Nat.card_eq_fintype_card, Fintype.card_coe, one_div, Finset.sum_const,
      nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_nat, ENNReal.toReal_inv, div_eq_mul_inv,
      ENNReal.one_toReal, one_mul, mul_inv]
    congr
    rw [Nat.card_eq_card_finite_toFinset]
  have C : H'.card = Nat.card H := by rw [← Nat.card_eq_card_finite_toFinset]; rfl
  simp only [this, one_div, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.sum_const, C,
    nsmul_eq_mul, ← mul_assoc]
  rw [mul_inv_cancel₀, one_mul]; swap
  · norm_cast
    exact Nat.card_pos.ne'
  have C₁ : Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) ≠ 0 := by
    have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) := h'A.to_subtype
    exact Nat.card_pos.ne'
  have C₃ : Nat.card H ≠ 0 := Nat.card_pos.ne'
  rw [← log_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- If $H$ is a finite subgroup of $G$, then
$\rho^-(U_H) = \log |A| - \log \max_t |A \cap (H+t)|$. -/
lemma rhoMinus_of_subgroup (H : AddSubgroup G) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (U : Ω → G) (hunif : IsUniform H U) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    rhoMinus U A = log (Nat.card A) -
      log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) := by
  apply le_antisymm _ (le_rhoMinus_of_subgroup H U hunif hA hU)
  rcases exists_card_inter_add_eq_sSup (A := A) H hA with ⟨t, ht, hpos⟩
  rw [← ht]
  have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) :=  (Nat.card_pos_iff.1 hpos).1
  exact rhoMinus_le_of_subgroup t U hunif hA nonempty_of_nonempty_subtype hU

/-- If $H$ is a finite subgroup of $G$, then
$\rho^+(U_H) = \log |H| - \log \max_t |A \cap (H+t)|$. -/
lemma rhoPlus_of_subgroup (H : AddSubgroup G) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)]
    (U : Ω → G) (hunif : IsUniform H U) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    rhoPlus U A = log (Nat.card H) -
      log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) := by
  have : H[U] = log (Nat.card H) := hunif.entropy_eq' (toFinite _) hU
  rw [rhoPlus, rhoMinus_of_subgroup H U hunif hA hU, this]
  abel

/-- We define $\rho(X) := (\rho^+(X) + \rho^-(X))/2$. -/
noncomputable def rho {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) : ℝ := ((rhoMinus X A) + (rhoPlus X A))/2

/-- We have $\rho(U_A) = 0$. -/
lemma rho_of_uniform {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (U : Ω → G) (A : Finset G) (hunif : IsUniform A U) (hU : Measurable U)
    (hA : A.Nonempty) : rho U A = 0 := by
  have : H[U] = log (Nat.card A) := hunif.entropy_eq' (toFinite _) hU
  simp only [rho, rhoPlus, this, Nat.card_eq_fintype_card, Fintype.card_coe, add_sub_cancel_right,
    add_self_div_two]
  apply le_antisymm _ (rhoMinus_nonneg _ hU)
  have Z := rhoMinus_le U A hU hA (fun _ ↦ 0) U hunif measurable_const hU (indepFun_const 0).symm
  have : (fun x ↦ 0) + U = U := by ext y; simp
  simpa [this] using Z

/-- If $H$ is a finite subgroup of $G$, and $\rho(U_H) \leq r$, then there exists $t$ such
that $|A \cap (H+t)| \geq e^{-r} \sqrt{|A||H|}$, and $|H|/|A| \in [e^{-2r}, e^{2r}]$. -/
lemma rho_of_subgroup (H: AddSubgroup G) {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (U : Ω → G)
    (hunif : IsUniform H U) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U)
    (r : ℝ) (hr : rho U A ≤ r) :
    ∃ t : G,
      exp (-r) * (Nat.card A * Nat.card H) ^ (1/2) ≤ Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)
      ∧ Nat.card A ≤ exp (2 * r) * Nat.card H
      ∧ Nat.card H ≤ exp (2 * r) * Nat.card A := by
  have hr' : rho U A ≤ r := hr
  have Hpos : 0 < (Nat.card H : ℝ) := by exact_mod_cast Nat.card_pos
  have : Nonempty A := hA.to_subtype
  have Apos : 0 < (Nat.card A : ℝ) := by exact_mod_cast Nat.card_pos
  simp only [rho] at hr
  rw [rhoMinus_of_subgroup H U hunif hA hU, rhoPlus_of_subgroup H U hunif hA hU] at hr
  rcases exists_card_inter_add_eq_sSup (A := A) H hA with ⟨t, ht, hpos⟩
  rw [← ht] at hr
  have Rm : 0 ≤ rhoMinus U A := rhoMinus_nonneg _ hU
  have RM : 0 ≤ rhoPlus U A := by
    rw [rhoPlus_of_subgroup H U hunif hA hU, ← ht, sub_nonneg]
    apply log_le_log (by exact_mod_cast hpos)
    norm_cast
    have : Nat.card (t +ᵥ (H : Set G) : Set G) = Nat.card H := by
      apply Nat.card_image_of_injective (add_right_injective t)
    rw [← this]
    exact Nat.card_mono (toFinite _) inter_subset_right
  have I : |log (Nat.card H) - log (Nat.card A)| ≤ 2 * r := calc
    |log (Nat.card H) - log (Nat.card A)|
    _ = |H[U] - log (Nat.card A)| := by rw [hunif.entropy_eq' (toFinite _) hU]; rfl
    _ = |rhoPlus U A - rhoMinus U A| := by congr 1; simp [rhoPlus]; abel
    _ ≤ rhoPlus U A + rhoMinus U A :=
      (abs_sub _ _).trans_eq (by simp [abs_of_nonneg, Rm, RM])
    _ = 2 * rho U A := by simp [rho]; ring
    _ ≤ 2 * r := by linarith
  refine ⟨t, ?_, ?_, ?_⟩
  · have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) := (Nat.card_pos_iff.1 hpos).1
    have : - r + (log (Nat.card A) + log (Nat.card H)) * (1/2) ≤
      log (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)) := by linarith
    have := exp_monotone this
    rwa [exp_add, exp_log (by exact_mod_cast hpos), exp_mul, exp_add,
      exp_log Hpos, exp_log Apos] at this
  · have : log (Nat.card A) ≤ 2 * r + log (Nat.card H) := by
      linarith [(abs_sub_le_iff.1 I).2]
    have := exp_monotone this
    rwa [exp_log Apos, exp_add, exp_log Hpos] at this
  · have : log (Nat.card H) ≤ 2 * r + log (Nat.card A) := by
      linarith [(abs_sub_le_iff.1 I).1]
    have := exp_monotone this
    rwa [exp_log Hpos, exp_add, exp_log Apos] at this

/-- For any $s \in G$, $\rho(X+s) = \rho(X)$. -/
lemma rho_of_translate {Ω : Type*} [MeasureSpace Ω]
    (X : Ω → G) (A : Finset G) (s:G) : rho (fun ω ↦ X ω + s) A = rho X A := by sorry

/-- \rho(X)$ depends continuously on the distribution of $X$. -/
lemma rho_continuous [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] {A} :
    Continuous fun μ : ProbabilityMeasure G ↦ @rho G _ hGm G ⟨μ⟩ id A := by sorry

/-- If $X,Y$ are independent, one has
  $$ \rho^-(X+Y) \leq \rho^-(X)$$ -/
lemma rhoMinus_of_sum {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G)
    (A : Finset G) (hindep: IndepFun X Y) : rhoMinus (X+Y) A ≤ rhoMinus X A := by sorry

/-- If $X,Y$ are independent, one has
$$ \rho^+(X+Y) \leq \rho^+(X) + \bbH[X+Y] - \bbH[X]$$ -/
lemma rhoPlus_of_sum {Ω : Type*} [MeasureSpace Ω]
    (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) :
    rhoPlus (X+Y) A ≤ rhoPlus X A + H[X+Y] - H[X] := by
  simp [rhoPlus]
  have := rhoMinus_of_sum X Y A hindep
  linarith

/-- If $X,Y$ are independent, one has
  $$ \rho(X+Y) \leq \rho(X) + \frac{1}{2}( \bbH[X+Y] - \bbH[X] ).$$
  -/
lemma rho_of_sum {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) :
    rho (X+Y) A ≤ rho X A + (H[X+Y] - H[X])/2 := by
  simp [rho, rhoPlus]
  have := rhoMinus_of_sum X Y A hindep
  linarith

-- This may not be the optimal spelling for condRho, feel free to improve
/-- We define $\rho(X|Y) := \sum_y {\bf P}(Y=y) \rho(X|Y=y)$. -/
noncomputable def condRho {Ω S : Type*}
    [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) : ℝ :=
  ∑' s, (volume (Y ⁻¹' {s})).toReal * @rho G _ _ Ω ⟨ ProbabilityTheory.cond volume (Y⁻¹' {s}) ⟩ X A

/-- Average of rhoMinus along the fibers-/
noncomputable def condRhoMinus {Ω S : Type*}
    [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) : ℝ :=
  ∑' s, (volume (Y ⁻¹' {s})).toReal *
    @rhoMinus G _ _ Ω ⟨ProbabilityTheory.cond volume (Y⁻¹' {s}) ⟩ X A

/-- Average of rhoPlus along the fibers-/
noncomputable def condRhoPlus {Ω S : Type*}
    [MeasureSpace Ω] (X : Ω → G) (Y : Ω → S) (A : Finset G) : ℝ :=
  ∑' s, (volume (Y ⁻¹' {s})).toReal *
    @rhoPlus G _ _ Ω ⟨ ProbabilityTheory.cond volume (Y⁻¹' {s}) ⟩ X A

/-- For any $s\in G$, $\rho(X+s|Y)=\rho(X|Y)$. -/
lemma condRho_of_translate {Ω S : Type*} [MeasureSpace Ω]
    (X : Ω → G) (Y : Ω → S) (A : Finset G) (s:G) :
    condRho (fun ω ↦ X ω + s) Y A = condRho X Y A := by
  simp only [condRho, rho_of_translate]

/-- If $f$ is injective, then $\rho(X|f(Y))=\rho(X|Y)$. -/
lemma condRho_of_injective {Ω S T : Type*} [MeasureSpace Ω]
    (X : Ω → G) (Y : Ω → S) (A : Finset G) (f: S → T) (hf: Function.Injective f) :
    condRho X (f ∘ Y) A = condRho X Y A := by
  sorry

/-- $$ \rho^-(X|Z) \leq \rho^-(X) + \bbH[X] - \bbH[X|Z]$$ -/
lemma condRhoMinus_le {Ω S : Type*} [MeasureSpace Ω] [MeasurableSpace S]
    (X : Ω → G) (Z : Ω → S) (A : Finset G) :
    condRhoMinus X Z A ≤ rhoMinus X A + H[ X ] - H[ X | Z ] := by sorry

/-- $$ \rho^+(X|Z) \leq \rho^+(X)$$ -/
lemma condRhoPlus_le {Ω S : Type*} [MeasureSpace Ω] [MeasurableSpace S]
    (X : Ω → G) (Z : Ω → S) (A : Finset G) : condRhoPlus X Z A ≤ rhoPlus X A := by sorry

/-- $$ \rho(X|Z) \leq \rho(X) + \frac{1}{2}( \bbH[X] - \bbH[X|Z] )$$ -/
lemma condRho_le {Ω S : Type*} [MeasureSpace Ω] [MeasurableSpace S]
    (X : Ω → G) (Z : Ω → S) (A : Finset G) :
    condRho X Z A ≤ rho X A + (H[ X ] - H[ X | Z ]) / 2 := by sorry

variable [Module (ZMod 2) G]

/-- If $X,Y$ are independent, then
  $$ \rho(X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$
 -/
lemma rho_of_sum_le {Ω : Type*} [MeasureSpace Ω]
    (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) :
    rho (X + Y) A ≤ (rho X A + rho Y A + d[ X # Y ]) / 2 := by sorry

/-- If $X,Y$ are independent, then
  $$ \rho(X | X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$ -/
lemma condRho_of_sum_le {Ω : Type*} [MeasureSpace Ω]
    (X Y : Ω → G) (A : Finset G) (hindep: IndepFun X Y) :

    condRho X (X + Y) A ≤ (rho X A + rho Y A + d[ X # Y ]) / 2 := by sorry



section phiMinimizer

/-- Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$. -/
noncomputable def phi {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G) (η : ℝ) (A : Finset G) : ℝ :=
  d[ X # Y ] + η * (rho X A + rho Y A)

/-- Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$
and define a \emph{$\phi$-minimizer} to be a pair of random variables $X,Y$ which minimizes $\phi[X;Y]$.-/
def phiMinimizes {Ω: Type uG} [MeasureSpace Ω] (X Y : Ω → G) (η:ℝ) (A: Finset G) : Prop := ∀ (Ω': Type uG) (_: MeasureSpace Ω') (X' Y' : Ω' → G), phi X Y η A ≤ phi X' Y' η A

variable (η:ℝ) (hη: η > 0) (A: Finset G)

/-- There exists a $\phi$-minimizer. -/
lemma phi_min_exists : ∃ (Ω: Type uG) (_:MeasureSpace Ω) (X Y : Ω → G), phiMinimizes X Y η A := by sorry

-- Let $(X_1, X_2)$ be a $\phi$-minimizer, and $\tilde X_1, \tilde X_2$ be independent copies of $X_1,X_2$ respectively.
variable {Ω: Type uG} [MeasureSpace Ω] (X₁ X₂ X'₁ X'₂ : Ω → G) (hmin: phiMinimizes X₁ X₂ η A) (hident₁: IdentDistrib X₁ X'₁) (hident₁: IdentDistrib X₂ X'₂) (hindep: iIndepFun (fun _ ↦ hGm) ![X₁, X₂, X'₁, X'₂])

local notation3 "I₁" => I[X₁ + X₂ : X'₁ + X₂ | X₁ + X₂ + X'₁ + X'₂]
local notation3 "I₂" => I[X₁ + X₂ : X₁ + X'₁ | X₁ + X₂ + X'₁ + X'₂]

/-- $I_1\le 2\eta d[X_1;X_2]$ -/
lemma I_one_le : I₁ ≤ 2 * η * d[ X₁ # X₂ ] := by sorry

/-- $d[X_1;X_1]+d[X_2;X_2]= 2d[X_1;X_2]+(I_2-I_1)$. -/
lemma dist_add_dist_eq : d[ X₁ # X₁ ] + d[ X₂ # X₂ ] = 2 * d[ X₁ # X₂ ] + (I₂ - I₁) := by sorry

/-- $I_2\le 2\eta d[X_1;X_2] + \frac{\eta}{1-\eta}(2\eta d[X_1;X_2]-I_1)$. -/
lemma I_two_le : I₂ ≤ 2 * η * d[ X₁ # X₂ ] + (η / (1 - η)) * (2 * η * d[ X₁ # X₂ ] - I₁) := by sorry

/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2]\le 3\bbI[T_1:T_2\mid T_3] + (2\bbH[T_3]-\bbH[T_1]-\bbH[T_2])+ \eta(\rho(T_1|T_3)+\rho(T_2|T_3)-\rho(X_1)-\rho(X_2)).$$ -/
lemma dist_le_of_sum_zero {Ω': Type uG} [MeasureSpace Ω'] (T₁ T₂ T₃ : Ω' → G) (hsum: T₁ + T₂ + T₃ = 0) : d[ X₁ # X₂ ] ≤ 3 * I[T₁ : T₂ | T₃] + (2 * H[T₃] - H[T₁] - H[T₂]) + η * (condRho T₁ T₃ A + condRho T₂ T₃ A - rho X₁ A - rho X₂ A) := by sorry

/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2] \leq \sum_{1 \leq i < j \leq 3} \bbI[T_i:T_j] + \frac{\eta}{3} \sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j) + \rho(T_j|T_i) -\rho(X_1)-\rho(X_2))$$
-/
lemma dist_le_of_sum_zero' {Ω': Type uG} [MeasureSpace Ω'] (T₁ T₂ T₃ : Ω' → G) (hsum: T₁ + T₂ + T₃ = 0) : d[ X₁ # X₂ ] ≤ I[T₁ : T₂] + I[T₁ : T₃] + I[T₂ : T₃] + (η/3) * ( ( condRho T₁ T₂ A + condRho T₂ T₁ A - rho X₁ A - rho X₂ A) +
( condRho T₁ T₃ A + condRho T₃ T₁ A - rho X₁ A - rho X₂ A) + ( condRho T₂ T₃ A + condRho T₃ T₂ A - rho X₁ A - rho X₂ A) ) := sorry

/-- For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define $S:=Y_1+Y_2+Y_3+Y_4$, $T_1:=Y_1+Y_2$, $T_2:=Y_1+Y_3$. Then
  $$\rho(T_1|T_2,S)+\rho(T_2|T_1,S) - \frac{1}{2}\sum_{i} \rho(Y_i)\le \frac{1}{2}(d[Y_1;Y_2]+d[Y_3;Y_4]+d[Y_1;Y_3]+d[Y_2;Y_4]).$$
-/
lemma condRho_sum_le {Ω': Type uG} [MeasureSpace Ω'] (Y₁ Y₂ Y₃ Y₄ : Ω' → G) (hindep: iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) :
  let S := Y₁ + Y₂ + Y₃ + Y₄
  let T₁ := Y₁ + Y₂
  let T₂ := Y₁ + Y₃
  condRho T₁ T₂ A + condRho T₂ T₁ A - (rho Y₁ A + rho Y₂ A + rho Y₃ A + rho Y₄ A)/2 ≤ (d[ Y₁ # Y₂ ] + d[ Y₃ # Y₄ ] + d[ Y₁ # Y₃ ] + d[ Y₂ # Y₄ ]) / 2 := by sorry

/-- For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define $T_1:=Y_1+Y_2,T_2:=Y_1+Y_3,T_3:=Y_2+Y_3$ and $S:=Y_1+Y_2+Y_3+Y_4$. Then
  $$\sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j,S) + \rho(T_j|T_i,S) - \frac{1}{2}\sum_{i} \rho(Y_i))\le \sum_{1\leq i < j \leq 4}d[Y_i;Y_j]$$ -/
lemma condRho_sum_le' {Ω': Type uG} [MeasureSpace Ω'] (Y₁ Y₂ Y₃ Y₄ : Ω' → G) (hindep: iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) :
  let S := Y₁ + Y₂ + Y₃ + Y₄
  let T₁ := Y₁ + Y₂
  let T₂ := Y₁ + Y₃
  let T₃ := Y₂ + Y₃
  condRho T₁ T₂ A + condRho T₂ T₁ A + condRho T₁ T₃ A + condRho T₃ T₁ A + condRho T₂ T₃ A + condRho T₃ T₂ A - 3*(rho Y₁ A + rho Y₂ A + rho Y₃ A + rho Y₄ A)/2 ≤ d[ Y₁ # Y₂ ] + d[ Y₁ # Y₃ ] + d[ Y₁ # Y₄ ] + d[ Y₂ # Y₃ ] + d[ Y₂ # Y₄ ] + d[ Y₃ # Y₄ ] := by sorry

/-- If $X_1,X_2$ is a $\phi$-minimizer, then $d[X_1;X_2] = 0$. -/
lemma dist_of_min_eq_zero (hη': η < 1/8) : d[ X₁ # X₂ ] = 0 := by sorry

end phiMinimizer

/-- For any random variables $Y_1,Y_2$, there exist a subgroup $H$ such that
  $$ 2\rho(U_H) \leq \rho(Y_1) + \rho(Y_2) + 8 d[Y_1;Y_2].$$ -/
theorem rho_PFR_conjecture (η:ℝ) (hη: η > 0) (hη': η < 1/8) {Ω: Type uG} [MeasureSpace Ω] (Y₁ Y₂: Ω → G) (A: Finset G):
    ∃ (H : AddSubgroup G) (Ω' : Type uG) (mΩ' : MeasureSpace Ω) (U : Ω → G),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ 2 * rho U A ≤ rho Y₁ A + rho Y₂ A + 8 * d[Y₁ # Y₂] := sorry

/-- If $|A+A| \leq K|A|$, then there exists a subgroup $H$ and $t\in G$ such that $|A \cap (H+t)| \geq K^{-4} \sqrt{|A||V|}$, and $|H|/|A|\in[K^{-8},K^8]$.
\end{corollary} -/
lemma better_PFR_conjecture_aux {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ 4 * Nat.card A ^ (1/2) * (Nat.card H : ℝ) ^ (-1/2 : ℝ)
      ∧ Nat.card H ≤ K ^ 8 * Nat.card A ∧ Nat.card A ≤ K ^ 8 * Nat.card H ∧ A ⊆ c + H := sorry

/-- If $A \subset {\bf F}_2^n$ is finite non-empty with $|A+A| \leq K|A|$, then there exists a subgroup $H$ of ${\bf F}_2^n$ with $|H| \leq |A|$ such that $A$ can be covered by at most $2K^9$ translates of $H$. -/
lemma better_PFR_conjecture {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 9 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := sorry
