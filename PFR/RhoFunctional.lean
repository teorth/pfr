import PFR.ForMathlib.CompactProb
import PFR.ForMathlib.Entropy.RuzsaDist
import PFR.Kullback
import Mathlib.MeasureTheory.Measure.AEMeasurable
import PFR.Mathlib.Probability.Independence.FourVariables
import PFR.Mathlib.Probability.Independence.ThreeVariables
import PFR.FirstEstimate
import PFR.ImprovedPFR


/-!
# The rho functional

Definition of the rho functional and basic facts

## Main definitions:

## Main results

-/


/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))


open MeasureTheory ProbabilityTheory Real Set Function Measure
open scoped Pointwise ENNReal
universe uG

section

variable {G : Type uG} [AddCommGroup G] [Fintype G] [hGm : MeasurableSpace G]
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

lemma nonempty_rhoMinusSet [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hA : A.Nonempty) :
    Set.Nonempty (rhoMinusSet X A μ) := by
  rcases eq_zero_or_isProbabilityMeasure μ with hμ | hμ
  · refine ⟨0, ⟨uniformOn (A : Set G), uniformOn_isProbabilityMeasure A.finite_toSet hA,
      by simp [hμ], by simp [hμ, KLDiv]⟩⟩
  obtain ⟨a, ha⟩ : ∃ x, x ∈ A := by exact hA
  set μ' := μ.map ((· - a) ∘ X) with hμ'
  set ν := uniformOn (A : Set G) with hν
  have : IsProbabilityMeasure μ' :=
    isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have : IsProbabilityMeasure ν :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
  refine ⟨_, ⟨μ', by infer_instance, fun y h ↦ ?_, rfl⟩⟩
  have h_indep : IndepFun Prod.fst Prod.snd (μ'.prod ν) := ProbabilityTheory.indepFun_fst_snd
  rw [← hν, h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp)] at h
  specialize h a (Finset.mem_univ a)
  have : (Measure.map Prod.snd (μ'.prod ν)) {a} ≠ 0 := by
    simp [Measure.map_snd_prod, ν, uniformOn_apply_singleton_of_mem (by exact ha) A.finite_toSet]
  simp only [mul_eq_zero, this, false_or, Measure.map_fst_prod] at h
  simp only [measure_univ, one_smul] at h
  rw [hμ', ← Measure.map_map (by fun_prop) hX,
    Measure.map_apply (by fun_prop) (measurableSet_singleton (y - a))] at h
  convert h
  ext z
  simp

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
    apply IdentDistrib.refl (by fun_prop)
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
    (hU : Measurable U) (hindep : IndepFun T U μ')
    (habs : ∀ y, (μ'.map (T + U)) {y} = 0 → μ.map X {y} = 0) :
    ρ⁻[X ; μ # A] ≤ KL[X ; μ # T + U ; μ'] := by
  have : IsProbabilityMeasure (Measure.map T μ') := isProbabilityMeasure_map hT.aemeasurable
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
  have E : Measure.map U μ' = uniformOn (A : Set G) := hunif.map_eq_uniformOn hU A.finite_toSet hA
  have M : (Measure.map (Prod.fst + Prod.snd) ((Measure.map T μ').prod (uniformOn ↑A))) =
      (Measure.map (T + U) μ') := by
    ext s _
    rw [hindep.map_add_eq_sum hT hU]
    have : IndepFun Prod.fst Prod.snd ((Measure.map T μ').prod (uniformOn (A : Set G))) :=
      ProbabilityTheory.indepFun_fst_snd
    rw [this.map_add_eq_sum measurable_fst measurable_snd,
      Measure.map_fst_prod, Measure.map_snd_prod]
    simp [E]
  apply csInf_le (bddBelow_rhoMinusSet hX)
  simp only [rhoMinusSet, Set.mem_setOf_eq]
  exact ⟨μ'.map T, isProbabilityMeasure_map hT.aemeasurable, by rwa [M], by simp [KLDiv, M]⟩

/-- For any $G$-valued random variable $X$, we define $\rho^+(X) := \rho^-(X) + \bbH(X) - \bbH(U_A)$. -/
noncomputable def rhoPlus (X : Ω → G) (A : Finset G) (μ : Measure Ω) : ℝ :=
  ρ⁻[X ; μ # A] + H[ X ; μ ] - log (Nat.card A)

@[inherit_doc rhoPlus] notation3:max "ρ⁺[" X " ; " μ " # " A "]" => rhoPlus X A μ

@[inherit_doc rhoPlus] notation3:max "ρ⁺[" X " # " A "]" => rhoPlus X A volume

lemma rhoPlus_eq_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {X' : Ω' → G} {μ' : Measure Ω'}
    (h : IdentDistrib X X' μ μ') : ρ⁺[X ; μ # A] = ρ⁺[X' ; μ' # A] := by
  simp [rhoPlus, rhoMinus_eq_of_identDistrib h, h.entropy_eq]

/-- We have $\rho^-(X) \geq 0$. -/
lemma rhoMinus_nonneg [IsZeroOrProbabilityMeasure μ]
    {X : Ω → G} {A : Finset G} (hX : Measurable X) : 0 ≤ ρ⁻[X ; μ # A] :=
  Real.sInf_nonneg (fun _ hx ↦ nonneg_of_mem_rhoMinusSet hX hx)

lemma rhoMinus_zero_measure (hP : μ = 0)
    {X : Ω → G} {A : Finset G} : ρ⁻[X ; μ # A] = 0 := by
  have : ∃ (μ' : Measure G), IsProbabilityMeasure μ' :=
    ⟨uniformOn Set.univ, uniformOn_isProbabilityMeasure finite_univ univ_nonempty⟩
  simp [rhoMinus, rhoMinusSet, hP, this, KLDiv]

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
  apply le_csInf (nonempty_rhoMinusSet hU hA)
  rintro - ⟨μ', hμ', habs, rfl⟩
  let T : G × G → G := Prod.fst
  have hT : Measurable T := measurable_fst
  let UA : G × G → G := Prod.snd
  have hUA : Measurable UA := measurable_snd
  letI : MeasureSpace (G × G) := ⟨μ'.prod (uniformOn (A : Set G))⟩
  have hprod : (ℙ : Measure (G × G)) = μ'.prod (uniformOn (A : Set G)) := rfl
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
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
      / (∑ h ∈ H', (volume.map (T + UA) {h}).toReal)) ≤ KL[U ; μ # T + UA ; ℙ] := by
    rw [I₁]
    apply Real.sum_mul_log_div_leq (by simp) (by simp) (fun i hi h'i ↦ ?_)
    simp [ENNReal.toReal_eq_zero_iff] at h'i
    have : (Measure.map U μ {i}).toReal = 0 := by simp [habs i h'i]
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

private lemma rhoMinus_le_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G}
    (t : G) {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty)
    (h'A : (A ∩ (t +ᵥ (H : Set G)) : Set G).Nonempty) (hU : Measurable U) :
    ρ⁻[U ; μ # A] ≤
      log (Nat.card A) - log (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)) := by
  have mapU : Measure.map U μ = uniformOn (H : Set G) :=
    hunif.map_eq_uniformOn hU (toFinite H) H.coe_nonempty
  obtain ⟨a, ha, h'a⟩ := by exact h'A
  rcases mem_vadd_set.1 h'a with ⟨v, vH, rfl⟩
  simp only [vadd_eq_add, Finset.mem_coe] at ha
  have P z : (fun x ↦ x - t) ⁻¹' {z} = {z + t} := by ext w; simp [sub_eq_iff_eq_add]
  set μ' := μ.map ((· - t) ∘ U) with hμ'
  have μ'_sing z : μ' {z} = uniformOn (H : Set G) {z + t} := by
    rw [hμ', ← Measure.map_map (by fun_prop) hU,
      Measure.map_apply (by fun_prop) (measurableSet_singleton _), mapU, P]
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
  have : IsProbabilityMeasure μ' :=
    isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have h_indep : IndepFun Prod.fst Prod.snd (μ'.prod (uniformOn (A : Set G))) := indepFun_fst_snd
  apply csInf_le (bddBelow_rhoMinusSet hU)
  simp only [rhoMinusSet, Nat.card_eq_fintype_card, Fintype.card_coe, mem_setOf_eq]
  refine ⟨μ', this, fun y h ↦ ?_, ?_⟩
  · rw [mapU]
    apply uniformOn_apply_singleton_of_nmem (fun yH ↦ ?_)
    rw [h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd,
      Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp), Measure.map_snd_prod,
      Measure.map_fst_prod] at h
    specialize h (t + v)
    simp only [Finset.mem_univ, measure_univ, one_smul,
      uniformOn_apply_singleton_of_mem (by exact ha) A.finite_toSet, Finset.coe_sort_coe,
      Nat.card_eq_fintype_card, Fintype.card_coe, one_div, μ'_sing, mul_eq_zero, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, false_or, true_implies] at h
    rw [uniformOn_apply_singleton_of_mem _ (toFinite (H : Set G))] at h
    · simp at h
    · convert (H.sub_mem yH vH) using 1
      abel
  let H' : Finset G := Set.Finite.toFinset (toFinite H)
  have hunif' : IsUniform H' U μ := by convert hunif; simp [H']
  rw [KLDiv_eq_sum, ← Finset.sum_subset (Finset.subset_univ H')]; swap
  · intro x _ hH
    rw [Measure.map_apply hU (measurableSet_singleton x), hunif.measure_preimage_of_nmem]
    · simp
    · simpa [H'] using hH
  have : ∑ x ∈ H', ((Measure.map U μ) {x}).toReal *
      log (((Measure.map U μ) {x}).toReal
        / ((Measure.map (Prod.fst + Prod.snd) (μ'.prod (uniformOn ↑A))) {x}).toReal)
      = ∑ x ∈ H', (1/Nat.card H) * log ((1/Nat.card H)
        / (Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) / (Nat.card A * Nat.card H))) := by
    apply Finset.sum_congr rfl (fun x hx ↦ ?_)
    have xH : x ∈ H := by simpa [H'] using hx
    have : (Measure.map U μ) {x} = 1/Nat.card H := by
      rw [Measure.map_apply hU (measurableSet_singleton _), hunif'.measure_preimage_of_mem hU hx]
      simp [H']
    simp only [this, one_div, ENNReal.toReal_inv, ENNReal.toReal_nat, Nat.cast_eq_zero]
    congr
    rw [h_indep.map_add_singleton_eq_sum measurable_fst measurable_snd, Measure.map_snd_prod,
      Measure.map_fst_prod]
    simp only [measure_univ, one_smul, μ'_sing]
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
lemma rhoMinus_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G}
    {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    ρ⁻[U ; μ # A] = log (Nat.card A) -
      log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) := by
  apply le_antisymm _ (le_rhoMinus_of_subgroup hunif hA hU)
  rcases exists_card_inter_add_eq_sSup (A := A) H hA with ⟨t, ht, hpos⟩
  rw [← ht]
  have : Nonempty (A ∩ (t +ᵥ (H : Set G)) : Set G) :=  (Nat.card_pos_iff.1 hpos).1
  exact rhoMinus_le_of_subgroup t hunif hA nonempty_of_nonempty_subtype hU

/-- If $H$ is a finite subgroup of $G$, then
$\rho^+(U_H) = \log |H| - \log \max_t |A \cap (H+t)|$. -/
lemma rhoPlus_of_subgroup [IsProbabilityMeasure μ] {H : AddSubgroup G}
    {U : Ω → G} (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U) :
    ρ⁺[U ; μ # A] = log (Nat.card H) -
      log (sSup {Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G) | t : G} : ℕ) := by
  have : H[U ; μ] = log (Nat.card H) := hunif.entropy_eq' (toFinite _) hU
  rw [rhoPlus, rhoMinus_of_subgroup hunif hA hU, this]
  abel

/-- We define $\rho(X) := (\rho^+(X) + \rho^-(X))/2$. -/
noncomputable def rho (X : Ω → G) (A : Finset G) (μ : Measure Ω ) : ℝ :=
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
      exp (-r) * (Nat.card A * Nat.card H) ^ (1/2) ≤ Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)
      ∧ Nat.card A ≤ exp (2 * r) * Nat.card H
      ∧ Nat.card H ≤ exp (2 * r) * Nat.card A := by
  have hr' : ρ[U ; μ # A] ≤ r := hr
  have Hpos : 0 < (Nat.card H : ℝ) := by exact_mod_cast Nat.card_pos
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
    have : Nat.card (t +ᵥ (H : Set G) : Set G) = Nat.card H := by
      apply Nat.card_image_of_injective (add_right_injective t)
    rw [← this]
    exact Nat.card_mono (toFinite _) inter_subset_right
  have I : |log (Nat.card H) - log (Nat.card A)| ≤ 2 * r := calc
    |log (Nat.card H) - log (Nat.card A)|
    _ = |H[U ; μ] - log (Nat.card A)| := by rw [hunif.entropy_eq' (toFinite _) hU]; rfl
    _ = |ρ⁺[U ; μ # A] - ρ⁻[U ; μ # A]| := by congr 1; simp [rhoPlus]; abel
    _ ≤ ρ⁺[U ; μ # A] + ρ⁻[U ; μ # A] :=
      (abs_sub _ _).trans_eq (by simp [abs_of_nonneg, Rm, RM])
    _ = 2 * ρ[U ; μ # A] := by simp [rho]; ring
    _ ≤ 2 * r := by linarith
  refine ⟨t, ?_, ?_, ?_⟩
  · have : - r + (log (Nat.card A) + log (Nat.card H)) * (1/2) ≤
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

/-- If $H$ is a finite subgroup of $G$, and $\rho(U_H) \leq r$, then there exists $t$ such
that $|A \cap (H+t)| \geq e^{-r} \sqrt{|A||H|}$, and $|H|/|A| \in [e^{-2r}, e^{2r}]$. -/
lemma rho_of_submodule [IsProbabilityMeasure μ] [Module (ZMod 2) G]
    {H : Submodule (ZMod 2) G} {U : Ω → G}
    (hunif : IsUniform H U μ) {A : Finset G} (hA : A.Nonempty) (hU : Measurable U)
    (r : ℝ) (hr : ρ[U ; μ # A] ≤ r) :
    ∃ t : G,
      exp (-r) * (Nat.card A * Nat.card H) ^ (1/2) ≤ Nat.card (A ∩ (t +ᵥ (H : Set G)) : Set G)
      ∧ Nat.card A ≤ exp (2 * r) * Nat.card H
      ∧ Nat.card H ≤ exp (2 * r) * Nat.card A :=
  rho_of_subgroup (H := H.toAddSubgroup) hunif hA hU r hr

/-- \rho(X)$ depends continuously on the distribution of $X$. -/
lemma rho_continuous [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G] {A} :
    Continuous fun μ : ProbabilityMeasure G ↦ ρ[(id : G → G) ; μ # A] := by sorry

/-- If $X,Y$ are independent, one has
  $$ \rho^-(X+Y) \leq \rho^-(X)$$ -/
lemma rhoMinus_of_sum [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y)
    (hA : A.Nonempty) (hindep : IndepFun X Y μ) :
    ρ⁻[X + Y ; μ # A] ≤ ρ⁻[X ; μ # A] := by
  rcases eq_zero_or_isProbabilityMeasure μ with hμ | hμ
  · simp [rhoMinus_zero_measure hμ]
  apply le_csInf (nonempty_rhoMinusSet hX hA)
  have : IsProbabilityMeasure (uniformOn (A : Set G)) :=
    uniformOn_isProbabilityMeasure A.finite_toSet hA
  rintro - ⟨μ', μ'_prob, habs, rfl⟩
  obtain ⟨Ω', hΩ', m, X', Y', T, U, hm, hindep', hX', hY', hT, hU, hXX', hYY', hTμ, hU_unif⟩ :=
    independent_copies4_nondep (X₁ := X) (X₂ := Y) (X₃ := id) (X₄ := id) hX hY measurable_id
    measurable_id μ μ μ' (uniformOn (A : Set G))
  let _ : MeasureSpace Ω' := ⟨m⟩
  have hP : (ℙ : Measure Ω') = m := rfl
  have hTU : IdentDistrib (T + U) (Prod.fst + Prod.snd) ℙ (μ'.prod (uniformOn (A : Set G))) := by
    apply IdentDistrib.add
    · exact hTμ.trans IdentDistrib.fst_id.symm
    · exact hU_unif.trans IdentDistrib.snd_id.symm
    · exact hindep'.indepFun (i := 2) (j := 3) (by simp)
    · exact indepFun_fst_snd
  have hXY : IdentDistrib (X + Y) (X' + Y') μ ℙ := by
    apply IdentDistrib.add hXX'.symm hYY'.symm hindep
    exact hindep'.indepFun zero_ne_one
  have hX'TUY' : IndepFun (⟨X', T + U⟩) Y' ℙ := by
    have I : iIndepFun (fun x ↦ hGm) ![X', Y', T + U] m :=
      ProbabilityTheory.iIndepFun.apply_two_last hindep' hX' hY' hT hU
        (phi := fun a b ↦ a + b) (by fun_prop)
    exact (I.reindex_three_bac.pair_last_of_three hY' hX' (by fun_prop)).symm
  have I₁ : ρ⁻[X + Y ; μ # A] ≤ KL[X + Y ; μ # (T + Y') + U ; ℙ] := by
    apply rhoMinus_le (by fun_prop) hA _ (by fun_prop) (by fun_prop)
    · have : iIndepFun (fun x ↦ hGm) ![U, X', T, Y'] := hindep'.reindex_four_dacb
      have : iIndepFun (fun x ↦ hGm) ![U, X', T + Y'] :=
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
    apply IdentDistrib.refl
    fun_prop
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
    (hX : Measurable X) (hY : Measurable Y) (hA : A.Nonempty) (hindep : IndepFun X Y μ) :
    ρ⁺[X + Y ; μ # A] ≤ ρ⁺[X ; μ # A] + H[X + Y ; μ] - H[X ; μ] := by
  simp [rhoPlus]
  have := rhoMinus_of_sum hX hY hA hindep
  linarith

/-- If $X,Y$ are independent, one has
  $$ \rho(X+Y) \leq \rho(X) + \frac{1}{2}( \bbH[X+Y] - \bbH[X] ).$$
  -/
lemma rho_of_sum [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hA : A.Nonempty) (hindep : IndepFun X Y μ) :
    ρ[X + Y ; μ # A] ≤ ρ[X ; μ # A] + (H[X+Y ; μ] - H[X ; μ])/2 := by
  simp [rho, rhoPlus]
  have := rhoMinus_of_sum hX hY hA hindep
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
    (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω): ℝ :=
  ∑' s, (μ (Y ⁻¹' {s})).toReal * ρ[X ; μ[|Y ← s] # A]

/-- Average of rhoMinus along the fibers-/
noncomputable def condRhoMinus {S : Type*}
    (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω) : ℝ :=
  ∑' s, (μ (Y ⁻¹' {s})).toReal * ρ⁻[X ; μ[|Y ← s] # A]

/-- Average of rhoPlus along the fibers-/
noncomputable def condRhoPlus {S : Type*}
    (X : Ω → G) (Y : Ω → S) (A : Finset G) (μ : Measure Ω) : ℝ :=
  ∑' s, (μ (Y ⁻¹' {s})).toReal * ρ⁺[X ; μ[|Y ← s] # A]

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

omit [Fintype G] [DiscreteMeasurableSpace G] in
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
  rw [M]
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
    [Fintype S] [MeasurableSingletonClass S]
    {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z) (hA : A.Nonempty) :
    ρ⁻[X | Z ; μ # A] ≤ ρ⁻[X ; μ # A] + H[X ; μ] - H[X | Z ; μ] := by
  have : IsProbabilityMeasure (uniformOn (A : Set G)) := by
    apply uniformOn_isProbabilityMeasure A.finite_toSet hA
  suffices ρ⁻[X | Z ; μ # A] - H[X ; μ] + H[X | Z ; μ] ≤ ρ⁻[X ; μ # A] by linarith
  apply le_csInf (nonempty_rhoMinusSet hX hA)
  rintro - ⟨μ', hμ', habs, rfl⟩
  rw [condRhoMinus, tsum_fintype]
  let _ : MeasureSpace (G × G) := ⟨μ'.prod (uniformOn (A : Set G))⟩
  have hP : (ℙ : Measure (G × G)) = μ'.prod (uniformOn (A : Set G)) := rfl
  have : IsProbabilityMeasure (ℙ : Measure (G × G)) := by rw [hP]; infer_instance
  have : ∑ b : S, (μ (Z ⁻¹' {b})).toReal * ρ⁻[X ; μ[|Z ← b] # A]
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
    [Fintype S] [MeasurableSingletonClass S]
    {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z) (hA : A.Nonempty) :
    ρ⁺[X | Z ; μ # A] ≤ ρ⁺[X ; μ # A] := by
  have : IsProbabilityMeasure (Measure.map Z μ) := isProbabilityMeasure_map hZ.aemeasurable
  have I₁ := condRhoMinus_le hX hZ hA (μ := μ)
  simp_rw [condRhoPlus, rhoPlus, tsum_fintype]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, tsub_le_iff_right]
  rw [← Finset.sum_mul, ← tsum_fintype, ← condRhoMinus, ← condEntropy_eq_sum_fintype _ _ _ hZ]
  simp_rw [← Measure.map_apply hZ (measurableSet_singleton _)]
  simp only [Finset.sum_toReal_measure_singleton, Finset.coe_univ, measure_univ, ENNReal.one_toReal,
    one_mul, sub_add_cancel, ge_iff_le]
  linarith

omit [Fintype G] [DiscreteMeasurableSpace G] in
lemma condRho_eq {S : Type*} [Fintype S] {Z : Ω → S} :
    ρ[X | Z ; μ # A] = (ρ⁻[X | Z ; μ # A] + ρ⁺[X | Z ; μ # A]) / 2 := by
  simp_rw [condRho, rho, ← mul_div_assoc, tsum_fintype, ← Finset.sum_div, mul_add,
    Finset.sum_add_distrib, ← tsum_fintype]
  rfl

/-- $$ \rho(X|Z) \leq \rho(X) + \frac{1}{2}( \bbH[X] - \bbH[X|Z] )$$ -/
lemma condRho_le [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S]
    [Fintype S] [MeasurableSingletonClass S]
    {Z : Ω → S} (hX : Measurable X) (hZ : Measurable Z) (hA : A.Nonempty) :
    ρ[X | Z ; μ # A] ≤ ρ[X ; μ # A] + (H[X ; μ] - H[X | Z ; μ]) / 2 := by
  rw [condRho_eq, rho]
  linarith [condRhoMinus_le hX hZ hA (μ := μ), condRhoPlus_le hX hZ hA (μ := μ)]

omit [Fintype G] [DiscreteMeasurableSpace G] in
lemma condRho_prod_eq_sum [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S]
    [Fintype S] [MeasurableSingletonClass S]
    {Z T : Ω → S} (hZ : Measurable Z) (hT : Measurable T) :
    ρ[X | ⟨Z, T⟩ ; μ # A] = ∑ g, (μ (T ⁻¹' {g})).toReal * ρ[X | Z ; μ[|T ← g] # A] := by
  rw [condRho, tsum_fintype, ← Finset.univ_product_univ, Finset.sum_product_right]
  congr 1 with w
  simp only [condRho, tsum_fintype, Finset.mul_sum]
  congr 1 with w'
  rw [← mul_assoc]
  have A : (fun a ↦ (Z a, T a)) ⁻¹' {(w', w)} = Z ⁻¹' {w'} ∩ T ⁻¹' {w} := by ext; simp
  congr 1
  · simp only [A, ProbabilityTheory.cond, Measure.smul_apply,
      Measure.restrict_apply (hZ (.singleton w')),
      smul_eq_mul, ENNReal.toReal_mul]
    rcases eq_bot_or_bot_lt (μ (T ⁻¹' {w})) with hw|hw
    · have : μ (Z ⁻¹' {w'} ∩ T ⁻¹' {w}) = 0 :=
        le_antisymm (le_trans (measure_mono Set.inter_subset_right) hw.le) bot_le
      simp [hw, this]
    · rw [← mul_assoc, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel, ENNReal.one_toReal, one_mul]
      exacts [hw.ne', by finiteness]
  · congr 1
    rw [A, cond_cond_eq_cond_inter' (hT (.singleton _)) (hZ (.singleton _)), Set.inter_comm]
    finiteness

/-- $$ \rho(X|Z) \leq \rho(X) + \frac{1}{2}( \bbH[X] - \bbH[X|Z] )$$, conditional version -/
lemma condRho_prod_le [IsProbabilityMeasure μ] {S : Type*} [MeasurableSpace S]
    [Fintype S] [MeasurableSingletonClass S]
    {Z T : Ω → S} (hX : Measurable X) (hZ : Measurable Z) (hT : Measurable T) (hA : A.Nonempty) :
    ρ[X | ⟨Z, T⟩ ; μ # A] ≤ ρ[X | T ; μ # A] + (H[X | T ; μ] - H[X | ⟨Z, T⟩ ; μ]) / 2 := by
  rw [condRho_prod_eq_sum hZ hT]
  have : ∑ g : S, (μ (T ⁻¹' {g})).toReal * ρ[ X | Z ; μ[|T ⁻¹' {g}] # A] ≤
    ∑ g : S, (μ (T ⁻¹' {g})).toReal *
      (ρ[X ; μ[|T ⁻¹' {g}] # A] + (H[X ; μ[|T ⁻¹' {g}]] - H[X | Z ; μ[|T ⁻¹' {g}]]) / 2) := by
    apply Finset.sum_le_sum (fun g hg ↦ ?_)
    rcases eq_or_ne (μ (T ⁻¹' {g})) 0 with hpg | hpg
    · simp [hpg]
    gcongr
    have hμ : IsProbabilityMeasure (μ[|T ⁻¹' {g}]) := cond_isProbabilityMeasure hpg
    exact condRho_le hX hZ hA
  apply this.trans_eq
  simp_rw [mul_add, mul_div, mul_sub, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_sub_distrib, condRho, tsum_fintype, condEntropy_eq_sum_fintype X T μ hT,
    condEntropy_prod_eq_sum μ hZ hT]

lemma condRho_prod_eq_of_indepFun [IsProbabilityMeasure μ]
    {X : Ω → G} {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {W W' : Ω → S} (hX : Measurable X) (hW : Measurable W)
    (hW' : Measurable W') (h : IndepFun (⟨X, W⟩) W' μ) :
    ρ[X | ⟨W, W'⟩ ; μ # A] = ρ[X | W ; μ # A] := by
  rw [condRho_prod_eq_sum hW hW']
  have : ρ[X | W ; μ # A] = ∑ z, (μ (W' ⁻¹' {z})).toReal * ρ[X | W ; μ # A] := by
    rw [← Finset.sum_mul, sum_measure_preimage_singleton' μ hW', one_mul]
  rw [this]
  congr with w
  rcases eq_or_ne (μ (W' ⁻¹' {w})) 0 with hw|hw
  · simp [hw]
  congr 1
  apply condRho_eq_of_identDistrib hX hW hX hW
  exact (h.identDistrib_cond (MeasurableSet.singleton w) (by fun_prop) hW' hw).symm

variable [Module (ZMod 2) G]

/-- If $X,Y$ are independent, then
  $$ \rho(X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$
 -/
lemma rho_of_sum_le [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hA : A.Nonempty) (hindep : IndepFun X Y μ) :
    ρ[X + Y ; μ # A] ≤ (ρ[X ; μ # A] + ρ[Y ; μ # A] + d[ X ; μ # Y ; μ]) / 2 := by
  have I : ρ[X + Y ; μ # A] ≤ ρ[X ; μ # A] + (H[X+Y ; μ] - H[X ; μ])/2 := rho_of_sum hX hY hA hindep
  have J : ρ[Y + X ; μ # A] ≤ ρ[Y ; μ # A] + (H[Y+X ; μ] - H[Y ; μ ])/2 :=
    rho_of_sum hY hX hA hindep.symm
  have : Y + X = X + Y := by abel
  rw [this] at J
  have : X - Y = X + Y := ZModModule.sub_eq_add _ _
  rw [hindep.rdist_eq hX hY, sub_eq_add_neg, this]
  linarith

/-- If $X,Y$ are independent, then
  $$ \rho(X | X+Y) \leq \frac{1}{2}(\rho(X)+\rho(Y) + d[X;Y]).$$ -/
lemma condRho_of_sum_le [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hA : A.Nonempty) (hindep : IndepFun X Y μ) :
    ρ[X | X + Y ; μ # A] ≤ (ρ[X ; μ # A] + ρ[Y ; μ # A] + d[ X ; μ # Y ; μ ]) / 2 := by
  have I : ρ[X | X + Y ; μ # A] ≤ ρ[X ; μ # A] + (H[X ; μ] - H[X | X + Y ; μ]) / 2 :=
    condRho_le hX (by fun_prop) hA
  have I' : H[X ; μ] - H[X | X + Y ; μ] = H[X + Y ; μ] - H[Y ; μ] := by
    rw [ProbabilityTheory.chain_rule'' _ hX (by fun_prop), entropy_add_right hX hY,
      IndepFun.entropy_pair_eq_add hX hY hindep]
    abel
  have J : ρ[Y | Y + X ; μ # A] ≤ ρ[Y ; μ # A] + (H[Y ; μ] - H[Y | Y + X ; μ]) / 2 :=
    condRho_le hY (by fun_prop) hA
  have J' : H[Y ; μ] - H[Y | Y + X ; μ] = H[Y + X ; μ] - H[X ; μ] := by
    rw [ProbabilityTheory.chain_rule'' _ hY (by fun_prop), entropy_add_right hY hX,
      IndepFun.entropy_pair_eq_add hY hX hindep.symm]
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
  rw [hindep.rdist_eq hX hY, sub_eq_add_neg, this]
  linarith

end

section phiMinimizer

variable {G : Type uG} [AddCommGroup G] [Fintype G] [hGm : MeasurableSpace G]
[DiscreteMeasurableSpace G] {Ω : Type*} [MeasureSpace Ω]
{X Y Z : Ω → G} {A : Finset G}

/-- Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$. -/
noncomputable def phi (X Y : Ω → G) (η : ℝ) (A : Finset G) : ℝ :=
  d[ X # Y ] + η * (ρ[X # A] + ρ[Y # A])

/-- Given $G$-valued random variables $X,Y$, define
$$ \phi[X;Y] := d[X;Y] + \eta(\rho(X) + \rho(Y))$$
and define a \emph{$\phi$-minimizer} to be a pair of random variables $X,Y$ which
minimizes $\phi[X;Y]$.-/
def phiMinimizes {Ω : Type*} [MeasureSpace Ω] (X Y : Ω → G) (η : ℝ) (A : Finset G) : Prop :=
  ∀ (Ω' : Type uG) (_ : MeasureSpace Ω') (X' Y' : Ω' → G),
    IsProbabilityMeasure (ℙ : Measure Ω') → Measurable X' → Measurable Y' →
    phi X Y η A ≤ phi X' Y' η A

lemma phiMinimizes_of_identDistrib {Ω' : Type*} [MeasureSpace Ω']
    {X Y : Ω → G} {X' Y' : Ω' → G} {η : ℝ} {A : Finset G}
    (h_min : phiMinimizes X Y η A) (h₁ : IdentDistrib X X') (h₂ : IdentDistrib Y Y') :
    phiMinimizes X' Y' η A := by
  have : phi X Y η A = phi X' Y' η A := by
    simp only [phi]
    rw [h₁.rdist_eq h₂, rho_eq_of_identDistrib h₁, rho_eq_of_identDistrib h₂]
  simpa [phiMinimizes, this] using h_min

lemma phiMinimizes_comm [IsProbabilityMeasure (ℙ : Measure Ω)] {X Y : Ω → G} {η : ℝ} {A : Finset G}
    (h_min : phiMinimizes X Y η A) : phiMinimizes Y X η A := by
  have : phi Y X η A = phi X Y η A := by
    simp only [phi]
    rw [rdist_symm]
    linarith
  simpa [phiMinimizes, this] using h_min

variable {η : ℝ} (hη : 0 < η)

/-- There exists a $\phi$-minimizer. -/
lemma phi_min_exists :
  ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X Y : Ω → G), phiMinimizes X Y η A := by sorry

-- Let $(X_1, X_2)$ be a $\phi$-minimizer, and $\tilde X_1, \tilde X_2$ be independent copies
-- of $X_1,X_2$ respectively.
variable {X₁ X₂ X₁' X₂' : Ω → G} (h_min : phiMinimizes X₁ X₂ η A)
  (h₁ : IdentDistrib X₁ X₁')
  (h₂ : IdentDistrib X₂ X₂')
  (h_indep : iIndepFun (fun _ ↦ hGm) ![X₁, X₂, X₁', X₂'])
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')


local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']
local notation3 "I₂" => I[X₁ + X₂ : X₁ + X₁' | X₁ + X₂ + X₁' + X₂']
/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[X₁ # X₂]

lemma le_rdist_of_phiMinimizes (h_min : phiMinimizes X₁ X₂ η A) {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
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
  have : phi X₁ X₂ η A ≤ phi Y₁ Y₂ η A := h_min _ _ _ _ m_prob measurable_fst measurable_snd
  have Id₁ : IdentDistrib Y₁ X₁' ℙ μ₁ :=
    ⟨measurable_fst.aemeasurable, hX₁'.aemeasurable, by simp [Y₁, hP, m]⟩
  have Id₂ : IdentDistrib Y₂ X₂' ℙ μ₂ :=
    ⟨measurable_snd.aemeasurable, hX₂'.aemeasurable, by simp [Y₂, hP, m]⟩
  have I : d[Y₁ # Y₂] = d[X₁' ; μ₁ # X₂' ; μ₂] := Id₁.rdist_eq Id₂
  have J : ρ[Y₁ # A] = ρ[X₁' ; μ₁ # A] := rho_eq_of_identDistrib Id₁
  have K : ρ[Y₂ # A] = ρ[X₂' ; μ₂ # A] := rho_eq_of_identDistrib Id₂
  simp only [phi, I, J, K] at this
  linarith

lemma le_rdist_of_phiMinimizes' (h_min : phiMinimizes X₁ X₂ η A) {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X₁' : Ω₁ → G} {X₂' : Ω₂ → G} (hX₁' : Measurable X₁') (hX₂' : Measurable X₂') :
    d[X₁ # X₂] ≤ d[X₁' ; μ₁ # X₂' ; μ₂] +
      η * (ρ[X₁' ; μ₁ # A] - ρ[X₁ # A]) + η * (ρ[X₂' ; μ₂ # A] - ρ[X₂ # A]) := by
  linarith [le_rdist_of_phiMinimizes h_min hX₁' hX₂' (μ₁ := μ₁) (μ₂ := μ₂)]

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

lemma condRho_le_condRuzsaDist_of_phiMinimizes {S T : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (h : phiMinimizes X₁ X₂ η A) (h1 : Measurable X₁') (h2 : Measurable X₂')
    {Z : Ω → S} {W : Ω → T} (hZ : Measurable Z) (hW : Measurable W) :
    k - η * (ρ[X₁' | Z # A] - ρ[X₁ # A]) - η * (ρ[X₂' | W # A] - ρ[X₂ # A])
      ≤ d[X₁' | Z # X₂' | W] := by
  have : IsProbabilityMeasure (Measure.map Z ℙ) := isProbabilityMeasure_map hZ.aemeasurable
  have : IsProbabilityMeasure (Measure.map W ℙ) := isProbabilityMeasure_map hW.aemeasurable
  have hz (a : ℝ) : a = ∑ z, (ℙ (Z ⁻¹' {z})).toReal * a := by
    simp_rw [← Finset.sum_mul,← Measure.map_apply hZ (MeasurableSet.singleton _),
      Finset.sum_toReal_measure_singleton]
    simp
  have hw (a : ℝ) : a = ∑ w, (ℙ (W ⁻¹' {w})).toReal * a := by
    simp_rw [← Finset.sum_mul,← Measure.map_apply hW (MeasurableSet.singleton _),
      Finset.sum_toReal_measure_singleton]
    simp
  rw [condRuzsaDist_eq_sum' h1 hZ h2 hW, hz d[X₁ # X₂],
    hz (ρ[X₁ # A]), hz (η * (ρ[X₂' | W # A] - ρ[X₂ # A])), condRho, tsum_fintype,
    ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro z _
  rw [condRho, tsum_fintype, hw ρ[X₂ # A],
    hw ( (ℙ (Z ⁻¹' {z})).toReal * k -
    η * ((ℙ (Z ⁻¹' {z})).toReal * ρ[X₁' ; ℙ[|Z ⁻¹' {z}] # A] - (ℙ (Z ⁻¹' {z})).toReal * ρ[X₁ # A])),
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro w _
  rcases eq_or_ne (ℙ (Z ⁻¹' {z})) 0 with hpz | hpz
  · simp [hpz]
  rcases eq_or_ne (ℙ (W ⁻¹' {w})) 0 with hpw | hpw
  · simp [hpw]
  set μ := ℙ[|Z ← z]
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure hpz
  set μ' := ℙ[|W ← w]
  have hμ' : IsProbabilityMeasure μ' := cond_isProbabilityMeasure hpw
  suffices d[X₁ # X₂] - η * (ρ[X₁' ; μ # A] - ρ[X₁ # A]) -
      η * (ρ[X₂' ; μ' # A] - ρ[X₂ # A]) ≤ d[X₁' ; μ # X₂'; μ'] by
    replace this := mul_le_mul_of_nonneg_left this
      (show 0 ≤ (ℙ (Z ⁻¹' {z})).toReal * (ℙ (W ⁻¹' {w})).toReal by positivity)
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
    rw [rho_eq_of_identDistrib h₂, (IdentDistrib.refl hX₁.aemeasurable).rdist_eq h₂]
    apply rho_of_sum_le hX₁ hX₂' hA
    simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
  have : ρ[X₂ + X₁' # A] ≤ (ρ[X₁ # A] + ρ[X₂ # A] + d[ X₁ # X₂ ]) / 2 := by
    rw [add_comm, rho_eq_of_identDistrib h₁, h₁.rdist_eq (IdentDistrib.refl hX₂.aemeasurable)]
    apply rho_of_sum_le hX₁' hX₂ hA
    simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 1 by decide)
  have : ρ[X₁ | X₁ + X₂' # A] ≤ (ρ[X₁ # A] + ρ[X₂ # A] + d[ X₁ # X₂ ]) / 2 := by
    rw [rho_eq_of_identDistrib h₂, (IdentDistrib.refl hX₁.aemeasurable).rdist_eq h₂]
    apply condRho_of_sum_le hX₁ hX₂' hA
    simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
  have : ρ[X₂ | X₂ + X₁' # A] ≤ (ρ[X₁ # A] + ρ[X₂ # A] + d[ X₁ # X₂ ]) / 2 := by
    have : ρ[X₂ | X₂ + X₁' # A] ≤ (ρ[X₂ # A] + ρ[X₁' # A] + d[ X₂ # X₁' ]) / 2 := by
      apply condRho_of_sum_le hX₂ hX₁' hA
      simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 2 by decide)
    have I : ρ[X₁' # A] = ρ[X₁ # A] := rho_eq_of_identDistrib h₁.symm
    have J : d[X₂ # X₁'] = d[X₁ # X₂] := by
      rw [rdist_symm, h₁.rdist_eq (IdentDistrib.refl hX₂.aemeasurable)]
    linarith
  nlinarith

/- *****************************************
Second estimate
********************************************* -/

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep in
lemma I_two_aux :
    d[X₁ # X₁] + d[X₂ # X₂] = d[X₁ + X₂' # X₂ + X₁'] + d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] + I₂ := by
  have Z : d[X₁' # X₁] + d[X₂' # X₂] = d[X₁' + X₂' # X₁ + X₂] + d[X₁' | X₁' + X₂' # X₁ | X₁ + X₂]
      + I[X₁' + X₁ : X₁ + X₂|X₁' + X₁ + X₂' + X₂] :=
    sum_of_rdist_eq_char_2' X₁' X₁ X₂' X₂ h_indep.reindex_four_cadb hX₁' hX₁ hX₂' hX₂
  have C₁ : X₁' + X₁ + X₂' + X₂ = X₁ + X₂ + X₁' + X₂' := by abel
  have C₂ : X₁' + X₁ = X₁ + X₁' := by abel
  have C₃ : d[X₁' # X₁] = d[X₁ # X₁] := h₁.symm.rdist_eq (IdentDistrib.refl hX₁.aemeasurable)
  have C₄ : d[X₂' # X₂] = d[X₂ # X₂] := h₂.symm.rdist_eq (IdentDistrib.refl hX₂.aemeasurable)
  have C₅ : d[X₁' + X₂' # X₁ + X₂] = d[X₁ + X₂' # X₂ + X₁'] := by
    apply IdentDistrib.rdist_eq
    · apply IdentDistrib.add h₁.symm (IdentDistrib.refl hX₂'.aemeasurable)
      · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 3 by decide)
      · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
    · rw [add_comm]
      apply IdentDistrib.add (IdentDistrib.refl hX₂.aemeasurable) h₁
      · simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 0 by decide)
      · simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 2 by decide)
  have C₆ : d[X₁' | X₁' + X₂' # X₁ | X₁ + X₂] = d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] := by
    have A : d[X₁' | X₁' + X₂' # X₁ | X₁ + X₂] = d[X₁ | X₁ + X₂' # X₁' | X₂ + X₁'] := by
      apply condRuzsaDist_of_copy hX₁' (by fun_prop) hX₁ (by fun_prop) hX₁ (by fun_prop) hX₁'
        (by fun_prop)
      · have : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂'⟩) := by
          apply h₁.symm.prod_mk (IdentDistrib.refl hX₂'.aemeasurable)
          · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 3 by decide)
          · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 3 by decide)
        exact this.comp (u := fun (a : G × G) ↦ (a.1, a.1 + a.2)) (by fun_prop)
      · rw [add_comm]
        have : IdentDistrib (⟨X₁, X₂⟩) (⟨X₁', X₂⟩) := by
          apply h₁.prod_mk (IdentDistrib.refl hX₂.aemeasurable)
          · simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 1 by decide)
          · simpa using h_indep.indepFun (show (2 : Fin 4) ≠ 1 by decide)
        exact this.comp (u := fun (a : G × G) ↦ (a.1, a.2 + a.1)) (by fun_prop)
    have B : d[X₁ | X₁ + X₂' # X₁' | X₂ + X₁'] = d[X₁ | X₁ + X₂' # X₂ | X₂ + X₁'] := by
      have J z w : d[X₁ ; ℙ[|(X₁ + X₂') ⁻¹' {z}] # X₁' ; ℙ[|(X₂ + X₁') ⁻¹' {w}]]
          = d[X₁ ; ℙ[|(X₁ + X₂') ⁻¹' {z}] # X₂ ; ℙ[|(X₂ + X₁') ⁻¹' {w}]] := by
        rw [← rdist_add_const hX₁ hX₂ (c := w)]
        apply ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable)
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
  have C₄ : d[X₂' # X₁'] = d[X₁ # X₂] := by rw [rdist_symm]; exact h₁.symm.rdist_eq h₂.symm
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
    rw [rho_eq_of_identDistrib h₁.symm,
      IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₁]
  have : ρ[X₂ + X₂' # A] ≤ (ρ[X₂ # A] + ρ[X₂ # A] + d[ X₂ # X₂ ]) / 2 := by
    refine (rho_of_sum_le hX₂ hX₂' hA
      (by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide))).trans_eq ?_
    rw [rho_eq_of_identDistrib h₂.symm,
      IdentDistrib.rdist_eq (IdentDistrib.refl hX₂.aemeasurable) h₂]
  have : ρ[X₁ | X₁ + X₁' # A] ≤ (ρ[X₁ # A] + ρ[X₁ # A] + d[ X₁ # X₁ ]) / 2 := by
    refine (condRho_of_sum_le hX₁ hX₁' hA
      (by simpa using h_indep.indepFun (show (0 : Fin 4) ≠ 2 by decide))).trans_eq ?_
    rw [rho_eq_of_identDistrib h₁.symm,
      IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₁]
  have : ρ[X₂ | X₂ + X₂' # A] ≤ (ρ[X₂ # A] + ρ[X₂ # A] + d[ X₂ # X₂ ]) / 2 := by
    refine (condRho_of_sum_le hX₂ hX₂' hA
      (by simpa using h_indep.indepFun (show (1 : Fin 4) ≠ 3 by decide))).trans_eq ?_
    rw [rho_eq_of_identDistrib h₂.symm,
      IdentDistrib.rdist_eq (IdentDistrib.refl hX₂.aemeasurable) h₂]
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
  $$d[X_1;X_2]\le 3\bbI[T_1:T_2\mid T_3] + (2\bbH[T_3]-\bbH[T_1]-\bbH[T_2])+ \eta(\rho(T_1|T_3)+\rho(T_2|T_3)-\rho(X_1)-\rho(X_2)).$$ -/
lemma dist_le_of_sum_zero {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    [IsProbabilityMeasure μ] {T₁ T₂ T₃ : Ω' → G}
    (hsum : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) :
    k ≤ 3 * I[T₁ : T₂ ; μ] + (2 * H[T₃ ; μ] - H[T₁ ; μ] - H[T₂ ; μ])
      + η * (ρ[T₁ | T₃ ; μ # A] + ρ[T₂ | T₃ ; μ #  A] - ρ[X₁ # A] - ρ[X₂ # A]) := by
  let _ : MeasureSpace Ω' := ⟨μ⟩
  have : μ = ℙ := rfl
  simp only [this]
  have : ∑ t, (ℙ (T₃ ⁻¹' {t})).toReal * d[ X₁ # X₂ ] ≤ ∑ t, (ℙ (T₃ ⁻¹' {t})).toReal *
      (d[T₁ ; ℙ[|T₃ ← t] # T₂ ; ℙ[|T₃ ← t]]
        + η * (ρ[T₁ ; ℙ[|T₃ ← t] # A] - ρ[X₁ # A]) + η * (ρ[T₂ ; ℙ[|T₃ ← t] # A] - ρ[X₂ # A])) := by
    apply Finset.sum_le_sum (fun t ht ↦ ?_)
    rcases eq_or_ne (ℙ (T₃ ⁻¹' {t})) 0 with h't | h't
    · simp [h't]
    have : IsProbabilityMeasure (ℙ[|T₃ ← t]) := cond_isProbabilityMeasure h't
    gcongr
    exact le_rdist_of_phiMinimizes' h_min hT₁ hT₂
  have : k ≤ ∑ x : G, (ℙ (T₃ ⁻¹' {x})).toReal * d[T₁ ; ℙ[|T₃ ← x] # T₂ ; ℙ[|T₃ ← x]] +
      η * (ρ[T₁ | T₃ # A] - ρ[X₁ # A]) + η * (ρ[T₂ | T₃ # A] - ρ[X₂ # A]) := by
    have S : ∑ i : G, (ℙ (T₃ ⁻¹' {i})).toReal = 1 := by
      have : IsProbabilityMeasure (Measure.map T₃ ℙ) := isProbabilityMeasure_map hT₃.aemeasurable
      simp [← Measure.map_apply hT₃ (measurableSet_singleton _)]
    simp_rw [← Finset.sum_mul, S, mul_add, Finset.sum_add_distrib, ← mul_assoc, mul_comm _ η,
      mul_assoc, ← Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_sub,
      ← Finset.sum_mul, S] at this
    simpa [mul_sub, condRho, tsum_fintype] using this
  have J : ∑ x : G, (ℙ (T₃ ⁻¹' {x})).toReal * d[T₁ ; ℙ[|T₃ ← x] # T₂ ; ℙ[|T₃ ← x]]
      ≤ 3 * I[T₁ : T₂] + 2 * H[T₃] - H[T₁] - H[T₂] := by
    have h2T₃ : T₃ = T₁ + T₂ :=
      calc T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hsum, _root_.zero_sub]; simp [ZModModule.neg_eq_self]
        _ = T₁ + T₂ := by rw [add_sub_cancel_right]
    subst h2T₃
    have := ent_bsg hT₁ hT₂ (μ := ℙ)
    simp_rw [integral_fintype _ Integrable.of_finite,
      Measure.map_apply hT₃ (measurableSet_singleton _)] at this
    exact this
  linarith

include h_min in
omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- If $G$-valued random variables $T_1,T_2,T_3$ satisfy $T_1+T_2+T_3=0$, then
  $$d[X_1;X_2]\le 3\bbI[T_1:T_2\mid T_3] + (2\bbH[T_3]-\bbH[T_1]-\bbH[T_2])+ \eta(\rho(T_1|T_3)+\rho(T_2|T_3)-\rho(X_1)-\rho(X_2)).$$ -/
lemma dist_le_of_sum_zero_cond {Ω' : Type*} [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω')] {T₁ T₂ T₃ S : Ω' → G}
    (hsum : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)
    (hS : Measurable S) :
    k ≤ 3 * I[T₁ : T₂ | S] + (2 * H[T₃ | S] - H[T₁ | S] - H[T₂ | S])
      + η * (ρ[T₁ | ⟨T₃, S⟩ # A] + ρ[T₂ | ⟨T₃, S⟩ #  A] - ρ[X₁ # A] - ρ[X₂ # A]) := by
  have hw (a : ℝ) : a = ∑ w, (ℙ (S ⁻¹' {w})).toReal * a := by
    have : IsProbabilityMeasure (map S ℙ) := isProbabilityMeasure_map hS.aemeasurable
    simp_rw [← Finset.sum_mul,← Measure.map_apply hS (MeasurableSet.singleton _),
      Finset.sum_toReal_measure_singleton]
    simp
  rw [condMutualInfo_eq_sum' hS, condEntropy_eq_sum_fintype _ _ _ hS,
    condEntropy_eq_sum_fintype _ _ _ hS, condEntropy_eq_sum_fintype _ _ _ hS,
    condRho_prod_eq_sum hT₃ hS, condRho_prod_eq_sum hT₃ hS, hw k, hw ρ[X₁ # A], hw ρ[X₂ # A]]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, mul_sub, mul_add]
  gcongr with g hg
  rcases eq_or_ne (ℙ (S ⁻¹' {g})) 0 with hpg | hpg
  · simp [hpg]
  set μ := ℙ[|S ← g]
  have hμ : IsProbabilityMeasure μ := cond_isProbabilityMeasure hpg
  have := dist_le_of_sum_zero (μ := μ) h_min hsum hT₁ hT₂ hT₃
  have := mul_le_mul_of_nonneg_left this (show 0 ≤ (ℙ (S ⁻¹' {g})).toReal by simp)
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
    (hindep : iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
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
    exact hindep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption) 0 1 2 3
      (by decide) (by decide) (by decide) (by decide)
  have : ρ[T₁ # A] ≤ (ρ[Y₁ # A] + ρ[Y₂ # A] + d[Y₁ # Y₂]) / 2 :=
    rho_of_sum_le hY₁ hY₂ hA (hindep.indepFun (i := 0) (j := 1) (by decide))
  have : ρ[T₁' # A] ≤ (ρ[Y₃ # A] + ρ[Y₄ # A] + d[Y₃ # Y₄]) / 2 :=
    rho_of_sum_le hY₃ hY₄ hA (hindep.indepFun (i := 2) (j := 3) (by decide))
  linarith

lemma new_gen_ineq_aux2 {Y₁ Y₂ Y₃ Y₄ : Ω → G}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
    (hindep : iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
    ρ[Y₁ + Y₂ | ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ # A] ≤
       (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 4
        + (d[Y₁ # Y₃] + d[Y₂ # Y₄]) / 4 + d[Y₁ | Y₁ + Y₃ # Y₂ | Y₂ + Y₄] / 2 := by
  set S := Y₁ + Y₂ + Y₃ + Y₄
  set T₁ := Y₁ + Y₂
  set T₂ := Y₁ + Y₃
  set T₁' := Y₃ + Y₄
  set T₂' := Y₂ + Y₄
  have I : IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩) := by
    refine (hindep.indepFun_prod_mk_prod_mk ?_ 0 2 1 3
      (by decide) (by decide) (by decide) (by decide))
    intro i; fin_cases i <;> assumption
  calc
  ρ[Y₁ + Y₂ | ⟨T₂, S⟩ # A]
    = ρ[Y₁ + Y₂ | ⟨T₂, T₂'⟩ # A] := by
      have : S = T₂ + T₂' := by simp only [S, T₂, T₂']; abel
      rw [this]
      let e : G × G ≃ G × G :=
        { toFun := fun p ↦ ⟨p.1, p.1 + p.2⟩
          invFun := fun p ↦ ⟨p.1, p.2 - p.1⟩
          left_inv := by intro ⟨a, b⟩; simp [add_assoc]
          right_inv := by intro ⟨a, b⟩; simp [add_assoc] }
      exact condRho_of_injective T₁ (⟨T₂, T₂'⟩) (f := e) (A := A) e.injective
  _ = ∑ w, (ℙ (⟨T₂, T₂'⟩ ⁻¹' {w})).toReal * ρ[Y₁ + Y₂ ; ℙ[|⟨T₂, T₂'⟩ ← w] # A] := by
    rw [condRho, tsum_fintype]
  _ ≤ ∑ w, (ℙ (⟨T₂, T₂'⟩ ⁻¹' {w})).toReal * ((ρ[Y₁ ; ℙ[|⟨T₂, T₂'⟩ ← w] # A]
      + ρ[Y₂ ; ℙ[|⟨T₂, T₂'⟩ ← w] # A] + d[Y₁ ; ℙ[|⟨T₂, T₂'⟩ ← w] # Y₂ ; ℙ[|⟨T₂, T₂'⟩ ← w]]) / 2) := by
    gcongr with w hw
    have : IndepFun Y₁ Y₂ (ℙ[|⟨T₂, T₂'⟩ ⁻¹' {w}]) := by
      have E : (⟨Y₁, Y₃⟩)⁻¹' {p | p.1 + p.2 = w.1} ∩ (⟨Y₂, Y₄⟩)⁻¹' {p | p.1 + p.2 = w.2}
        = ⟨T₂, T₂'⟩ ⁻¹' {w} := by aesop
      have I : IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩) (ℙ[|(⟨Y₁, Y₃⟩)⁻¹' {p | p.1 + p.2 = w.1}
          ∩ (⟨Y₂, Y₄⟩)⁻¹' {p | p.1 + p.2 = w.2}]) :=
        I.cond (measurable_add (.singleton w.1))
          (measurable_add (.singleton w.2)) (hY₁.prod_mk hY₃) (hY₂.prod_mk hY₄)
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
    rw [J.measure_inter_preimage_eq_mul _ _ (.singleton x)
      (.singleton y), ENNReal.toReal_mul]
    rcases eq_or_ne (ℙ ((Y₁ + Y₃) ⁻¹' {x})) 0 with h1|h1
    · simp [h1]
    rcases eq_or_ne (ℙ ((Y₂ + Y₄) ⁻¹' {y})) 0 with h2|h2
    · simp [h2]
    congr 1
    have A : IdentDistrib Y₁ Y₁ (ℙ[|(Y₁ + Y₃) ⁻¹' {x} ∩ (Y₂ + Y₄) ⁻¹' {y}])
        (ℙ[|(Y₁ + Y₃) ⁻¹' {x}]) := by
      rw [← cond_cond_eq_cond_inter']
      have : IsProbabilityMeasure (ℙ[|(Y₁ + Y₃) ⁻¹' {x}]) := cond_isProbabilityMeasure h1
      apply (IndepFun.identDistrib_cond _ (.singleton _) hY₁ (by fun_prop) _).symm
      · have : IndepFun (⟨Y₁, Y₃⟩) (⟨Y₂, Y₄⟩) (ℙ[|(⟨Y₁, Y₃⟩) ⁻¹' {p | p.1 + p.2 = x}]) :=
          I.cond_left (measurable_add (.singleton x))
            (hY₁.prod_mk hY₃)
        exact this.comp measurable_fst measurable_add
      · rw [cond_apply, J.measure_inter_preimage_eq_mul _ _ (.singleton x) (.singleton y)]
        simp [h1, h2]
        · exact hY₁.add hY₃ (.singleton _)
      · exact hY₁.add hY₃ (.singleton _)
      · exact hY₂.add hY₄ (.singleton _)
      · finiteness
    have B : IdentDistrib Y₂ Y₂ (ℙ[|(Y₁ + Y₃) ⁻¹' {x} ∩ (Y₂ + Y₄) ⁻¹' {y}])
        (ℙ[|(Y₂ + Y₄) ⁻¹' {y}]) := by
      rw [Set.inter_comm, ← cond_cond_eq_cond_inter']
      have : IsProbabilityMeasure (ℙ[|(Y₂ + Y₄) ⁻¹' {y}]) := cond_isProbabilityMeasure h2
      apply (IndepFun.identDistrib_cond _ (.singleton _) hY₂ (hY₁.add hY₃) _).symm
      · have : IndepFun (⟨Y₂, Y₄⟩) (⟨Y₁, Y₃⟩) (ℙ[|(⟨Y₂, Y₄⟩) ⁻¹' {p | p.1 + p.2 = y}]) :=
          I.symm.cond_left (measurable_add (.singleton y))
            (hY₂.prod_mk hY₄)
        exact this.comp measurable_fst measurable_add
      · rw [Pi.add_def, cond_apply (hY₂.add hY₄ (.singleton y)), ← Pi.add_def, ← Pi.add_def,
          J.symm.measure_inter_preimage_eq_mul _ _ (.singleton _) (.singleton _)]
        simp [h1, h2]
      · exact hY₂.add hY₄ (.singleton _)
      · exact hY₁.add hY₃ (.singleton _)
      · finiteness
    exact IdentDistrib.rdist_eq A B
  _ = (ρ[Y₁ | T₂ # A] + ρ[Y₂ | T₂' # A] + d[Y₁ | T₂ # Y₂ | T₂']) / 2 := by
    congr 3
    · apply condRho_prod_eq_of_indepFun hY₁ (by fun_prop) (by fun_prop)
      exact I.comp (measurable_fst.prod_mk measurable_add) measurable_add
    · have : ρ[Y₂ | ⟨T₂, T₂'⟩ # A] = ρ[Y₂ | ⟨T₂', T₂⟩ # A] :=
        condRho_of_injective Y₂ (⟨T₂', T₂⟩) (f := Prod.swap) Prod.swap_injective
      rw [this]
      apply condRho_prod_eq_of_indepFun hY₂ (by fun_prop) (by fun_prop)
      exact I.symm.comp (measurable_fst.prod_mk measurable_add) measurable_add
  _ ≤ ((ρ[Y₁ # A] + ρ[Y₃ # A] + d[Y₁ # Y₃]) / 2 +
       (ρ[Y₂ # A] + ρ[Y₄ # A] + d[Y₂ # Y₄]) / 2 + d[Y₁ | T₂ # Y₂ | T₂']) / 2 := by
    gcongr
    · exact condRho_of_sum_le hY₁ hY₃ hA (hindep.indepFun (i := 0) (j := 2) (by decide))
    · exact condRho_of_sum_le hY₂ hY₄ hA (hindep.indepFun (i := 1) (j := 3) (by decide))
  _ = (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 4
        + (d[Y₁ # Y₃] + d[Y₂ # Y₄]) / 4 + d[Y₁ | Y₁ + Y₃ # Y₂ | Y₂ + Y₄] / 2 := by ring

lemma new_gen_ineq {Y₁ Y₂ Y₃ Y₄ : Ω → G}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
    (hindep : iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
    ρ[Y₁ + Y₂ | ⟨Y₁ + Y₃, Y₁ + Y₂ + Y₃ + Y₄⟩ # A] ≤
      (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 4
        + (d[Y₁ # Y₂] + d[Y₃ # Y₄] + d[Y₁ # Y₃] + d[Y₂ # Y₄]) / 8 + (d[Y₁ + Y₂ # Y₃ + Y₄]
          + I[Y₁ + Y₂ : Y₁ + Y₃ | Y₁ + Y₂ + Y₃ + Y₄] + d[Y₁ | Y₁ + Y₃ # Y₂ | Y₂ + Y₄]) / 4 := by
  have := new_gen_ineq_aux1 hY₁ hY₂ hY₃ hY₄ hindep hA
  have := new_gen_ineq_aux2 hY₁ hY₂ hY₃ hY₄ hindep hA
  linarith

/-- For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define
$S:=Y_1+Y_2+Y_3+Y_4$, $T_1:=Y_1+Y_2$, $T_2:=Y_1+Y_3$. Then
  $$\rho(T_1|T_2,S)+\rho(T_2|T_1,S) - \frac{1}{2}\sum_{i} \rho(Y_i)
    \le \frac{1}{2}(d[Y_1;Y_2]+d[Y_3;Y_4]+d[Y_1;Y_3]+d[Y_2;Y_4]).$$
-/
lemma condRho_sum_le {Y₁ Y₂ Y₃ Y₄ : Ω → G}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
    (hindep : iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
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
    new_gen_ineq hY₁ hY₂ hY₃ hY₄ hindep hA
  have J' : ρ[T₂ | ⟨T₁, Y₁ + Y₃ + Y₂ + Y₄⟩ # A] ≤
    (ρ[Y₁ # A] + ρ[Y₃ # A] + ρ[Y₂ # A] + ρ[Y₄ # A]) / 4
      + (d[Y₁ # Y₃] + d[Y₂ # Y₄] + d[Y₁ # Y₂] + d[Y₃ # Y₄]) / 8 + (d[Y₁ + Y₃ # Y₂ + Y₄]
        + I[Y₁ + Y₃ : Y₁ + Y₂|Y₁ + Y₃ + Y₂ + Y₄] + d[Y₁ | Y₁ + Y₂ # Y₃ | Y₃ + Y₄]) / 4 :=
    new_gen_ineq hY₁ hY₃ hY₂ hY₄ hindep.reindex_four_acbd hA
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
    rw [sum_of_rdist_eq_char_2' Y₁ Y₂ Y₃ Y₄ hindep hY₁ hY₂ hY₃ hY₄,
      sum_of_rdist_eq_char_2' Y₁ Y₃ Y₂ Y₄ hindep.reindex_four_acbd hY₁ hY₃ hY₂ hY₄, K, K', K'']
    abel
  linarith

/-- For independent random variables $Y_1,Y_2,Y_3,Y_4$ over $G$, define
$T_1:=Y_1+Y_2, T_2:=Y_1+Y_3, T_3:=Y_2+Y_3$ and $S:=Y_1+Y_2+Y_3+Y_4$. Then
  $$\sum_{1 \leq i < j \leq 3} (\rho(T_i|T_j,S) + \rho(T_j|T_i,S)
    - \frac{1}{2}\sum_{i} \rho(Y_i))\le \sum_{1\leq i < j \leq 4}d[Y_i;Y_j]$$ -/
lemma condRho_sum_le' {Y₁ Y₂ Y₃ Y₄ : Ω → G}
      (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hY₃ : Measurable Y₃) (hY₄ : Measurable Y₄)
      (hindep : iIndepFun (fun _ ↦ hGm) ![Y₁, Y₂, Y₃, Y₄]) (hA : A.Nonempty) :
    let S := Y₁ + Y₂ + Y₃ + Y₄
    let T₁ := Y₁ + Y₂
    let T₂ := Y₁ + Y₃
    let T₃ := Y₂ + Y₃
    ρ[T₁ | ⟨T₂, S⟩ # A] + ρ[T₂ | ⟨T₁, S⟩ # A] + ρ[T₁ | ⟨T₃, S⟩ # A] + ρ[T₃ | ⟨T₁, S⟩ # A]
      + ρ[T₂ | ⟨T₃, S⟩ # A] + ρ[T₃ | ⟨T₂, S⟩ # A]
      - 3 * (ρ[Y₁ # A] + ρ[Y₂ # A] + ρ[Y₃ # A] + ρ[Y₄ # A]) / 2 ≤
    d[Y₁ # Y₂] + d[Y₁ # Y₃] + d[Y₁ # Y₄] + d[Y₂ # Y₃] + d[Y₂ # Y₄] + d[Y₃ # Y₄] := by
  have K₁ := condRho_sum_le hY₁ hY₂ hY₃ hY₄ hindep hA
  have K₂ := condRho_sum_le hY₂ hY₁ hY₃ hY₄ hindep.reindex_four_bacd hA
  have Y₂₁ : Y₂ + Y₁ = Y₁ + Y₂ := by abel
  have dY₂₁ : d[Y₂ # Y₁] = d[Y₁ # Y₂] := rdist_symm
  rw [Y₂₁, dY₂₁] at K₂
  have K₃ := condRho_sum_le hY₃ hY₁ hY₂ hY₄ hindep.reindex_four_cabd hA
  have Y₃₁ : Y₃ + Y₁ = Y₁ + Y₃ := by abel
  have Y₃₂ : Y₃ + Y₂ = Y₂ + Y₃ := by abel
  have S₃ : Y₁ + Y₃ + Y₂ + Y₄ = Y₁ + Y₂ + Y₃ + Y₄ := by abel
  have dY₃₁ : d[Y₃ # Y₁] = d[Y₁ # Y₃] := rdist_symm
  have dY₃₂ : d[Y₃ # Y₂] = d[Y₂ # Y₃] := rdist_symm
  rw [Y₃₁, Y₃₂, S₃, dY₃₁, dY₃₂] at K₃
  linarith

include hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min hη in
/-- If $X_1, X_2$ is a $\phi$-minimizer, then $d[X_1;X_2] = 0$. -/
lemma dist_of_min_eq_zero' (hA : A.Nonempty) (hη' : η < 1/8) : d[X₁ # X₂] = 0 := by
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
    have : d[X₁ # X₁'] = d[X₁ # X₁] :=
      IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₁.symm
    have : d[X₁ # X₂'] = d[X₁ # X₂] :=
      IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
    have : d[X₂ # X₁'] = d[X₁ # X₂] := by
      rw [rdist_symm]
      exact IdentDistrib.rdist_eq h₁.symm (IdentDistrib.refl hX₂.aemeasurable)
    have : d[X₂ # X₂'] = d[X₂ # X₂] :=
      IdentDistrib.rdist_eq (IdentDistrib.refl hX₂.aemeasurable) h₂.symm
    have : d[X₁' # X₂'] = d[X₁ # X₂] := IdentDistrib.rdist_eq h₁.symm h₂.symm
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
theorem dist_of_min_eq_zero (hA : A.Nonempty) (hη' : η < 1/8) : d[X₁ # X₂] = 0 := by
  let ⟨Ω', m', μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1', h_id2'⟩
    := independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_eq h_id2]
  letI : MeasureSpace Ω' := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure Ω') := hμ
  have h'_min : phiMinimizes Y₁ Y₂ η A := phiMinimizes_of_identDistrib h_min h_id1.symm h_id2.symm
  exact dist_of_min_eq_zero' hη h'_min (h_id1.trans h_id1'.symm) (h_id2.trans h_id2'.symm)
     h_indep hY₁ hY₂ hY₁' hY₂'  hA hη'

open Filter
open scoped Topology

/-- For `η ≤ 1/8`, there exist τ-minimizers `X₁, X₂` at zero Rusza distance. For `η < 1/8`,
all minimizers are fine, by `tau_strictly_decreases'`. For `η = 1/8`, we use a limit of
minimizers for `η < 1/8`, which exists by compactness. -/
lemma phiMinimizer_exists_rdist_eq_zero (hA : A.Nonempty) :
    ∃ (Ω : Type uG) (_ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
      Measurable X₁ ∧ Measurable X₂ ∧ IsProbabilityMeasure (ℙ : Measure Ω)
      ∧ phiMinimizes X₁ X₂ (1/8 : ℝ) A ∧ d[X₁ # X₂] = 0 := by sorry

end phiMinimizer

section PFR

variable {G : Type uG} [AddCommGroup G] [Fintype G]  [Module (ZMod 2) G]
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
      rw [Measure.map_apply hX₁ $ .of_discrete]
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
    K ^ (-4) * (Nat.card A * Nat.card H) ^ (1/2) ≤ Nat.card (A ∩ (H + {t}) : Set G)
      ∧ Nat.card A ≤ K ^ 8 * Nat.card H ∧ Nat.card H ≤ K ^ 8 * Nat.card A := by
  have A_fin : Finite A := by infer_instance
  classical
  let mG : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := ⟨λ _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' h₀A hA
  let A' := A.toFinite.toFinset
  have h₀A' : Finset.Nonempty A' := by
    simp [A', Finset.Nonempty]
    exact h₀A
  have hAA' : A' = A := Finite.coe_toFinset (toFinite A)
  rcases exists_isUniform_measureSpace A' h₀A' with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -⟩
  rw [hAA'] at UAunif
  have hadd_sub : A + A = A - A := by ext; simp [mem_add, mem_sub, ZModModule.sub_eq_add]
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
  have J : K ^ (-4) = exp (-r) := by
    rw [hr, ← neg_mul, mul_comm, exp_mul, exp_log K_pos]
  have J' : K ^ 8 = exp (2 * r) := by
    have : 2 * r = 8 * log K := by ring
    rw [this, mul_comm, exp_mul, exp_log K_pos]
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
    Nat.card c ≤ K ^ 5 * Nat.card A ^ (1/2) * (Nat.card H : ℝ) ^ (-1/2)
      ∧ Nat.card H ≤ K ^ 8 * Nat.card A ∧ Nat.card A ≤ K ^ 8 * Nat.card H ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' h₀A hA
  rcases better_PFR_conjecture_aux0 h₀A hA with ⟨H, x₀, J, IAH, IHA⟩
  have H_pos : (0 : ℝ) < Nat.card H := by
    have : 0 < Nat.card H := Nat.card_pos
    positivity
  have Hne : Set.Nonempty (A ∩ (H + {x₀})) := by
    by_contra h'
    have : 0 < Nat.card H := Nat.card_pos
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    simp only [Nat.card_eq_fintype_card, Nat.card_of_isEmpty, CharP.cast_eq_zero, lt_self_iff_false,
      not_nonempty_iff_eq_empty.1 h', Fintype.card_ofIsEmpty] at this
    /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  rcases Set.exists_subset_add_sub (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne with
    ⟨u, hu, Au, -⟩
  have Iu : Nat.card u ≤ K ^ 5 * Nat.card A ^ (1/2) * Nat.card H ^ (-1/2) := by
    have : (0 : ℝ) ≤ Nat.card u := by simp
    have Z1 := mul_le_mul_of_nonneg_left J this
    have Z2 : (Nat.card u * Nat.card (A ∩ (H + {x₀}) : Set G) : ℝ)
      ≤ Nat.card (A + A ∩ (↑H + {x₀})) := by norm_cast
    have Z3 : (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ) ≤ K * Nat.card A := by
      apply le_trans _ hA
      simp only [Nat.cast_le]
      apply Nat.card_mono (toFinite _)
      apply add_subset_add_left inter_subset_left
    have : 0 ≤ K ^ (4) * Nat.card A ^ (-1/2) * Nat.card H ^ (-1/2) := by positivity
    have T := mul_le_mul_of_nonneg_left ((Z1.trans Z2).trans Z3) this
    convert T using 1 <;> rpow_ring <;> norm_num
  have A_subset_uH : A ⊆ u + H := by
    apply Au.trans
    rw [add_sub_assoc]
    apply add_subset_add_left
    apply (sub_subset_sub inter_subset_right inter_subset_right).trans
    rintro - ⟨-, ⟨y, hy, xy, hxy, rfl⟩, -, ⟨z, hz, xz, hxz, rfl⟩, rfl⟩
    simp only [mem_singleton_iff] at hxy hxz
    simpa [hxy, hxz] using H.sub_mem hy hz
  exact ⟨H, u, Iu, IHA, IAH, A_subset_uH⟩

/-- If $A \subset {\bf F}_2^n$ is finite non-empty with $|A+A| \leq K|A|$, then there exists a
subgroup $H$ of ${\bf F}_2^n$ with $|H| \leq |A|$ such that $A$ can be covered by at most $2K^9$
translates of $H$. -/
lemma better_PFR_conjecture {A : Set G} (h₀A : A.Nonempty) {K : ℝ}
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G),
      Nat.card c < 2 * K ^ 9 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux' h₀A hA
  -- consider the subgroup `H` given by Lemma `PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : Submodule (ZMod 2) G) (c : Set G),
    Nat.card c ≤ K ^ 5 * Nat.card A ^ (1/2) * Nat.card H ^ (-1/2)
      ∧ Nat.card H ≤ K ^ 8 * Nat.card A ∧ Nat.card A ≤ K ^ 8 * Nat.card H
      ∧ A ⊆ c + H :=
    better_PFR_conjecture_aux h₀A hA
  have H_pos : (0 : ℝ) < Nat.card H := by
    have : 0 < Nat.card H := Nat.card_pos; positivity
  rcases le_or_lt (Nat.card H) (Nat.card A) with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ 5 * Nat.card A ^ (1/2) * Nat.card H ^ (-1/2) := hc
    _ ≤ K ^ 5 * (K ^ 8 * Nat.card H) ^ (1/2) * Nat.card H ^ (-1/2) := by
      gcongr
    _ = K ^ 9 := by rpow_ring; norm_num
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
    _ ≤ (K ^ 5 * Nat.card A ^ (1 / 2) * (Nat.card H ^ (-1 / 2)))
          * (Nat.card H / Nat.card H') := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ 5 * Nat.card A ^ (1 / 2) * (Nat.card H ^ (-1 / 2)))
          * (Nat.card H / (Nat.card A / 2)) := by
        gcongr
    _ = 2 * K ^ 5 * Nat.card A ^ (-1/2) * Nat.card H ^ (1/2) := by
        field_simp
        rpow_ring
        norm_num
    _ ≤ 2 * K ^ 5 * Nat.card A ^ (-1/2) * (K ^ 8 * Nat.card A) ^ (1/2) := by
        gcongr
    _ = 2 * K ^ 9 := by
        rpow_ring
        norm_num

/-- Corollary of `better_PFR_conjecture` in which the ambient group is not required to be finite
(but) then $H$ and $c$ are finite. -/
theorem better_PFR_conjecture' {G : Type*} [AddCommGroup G] [Module (ZMod 2) G]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (Afin : A.Finite)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : Submodule (ZMod 2) G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 9 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  let G' := Submodule.span (ZMod 2) A
  let G'fin : Fintype G' := (Afin.submoduleSpan _).fintype
  let ι : G'→ₗ[ZMod 2] G := G'.subtype
  have ι_inj : Injective ι := G'.toAddSubgroup.subtype_injective
  let A' : Set G' := ι ⁻¹' A
  have A_rg : A ⊆ range ι := by
    simp only [AddMonoidHom.coe_coe, Submodule.coe_subtype, Subtype.range_coe_subtype, G', ι]
    exact Submodule.subset_span
  have cardA' : Nat.card A' = Nat.card A := Nat.card_preimage_of_injective ι_inj A_rg
  have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
    rwa [cardA', ← preimage_add _ ι_inj A_rg A_rg,
         Nat.card_preimage_of_injective ι_inj (add_subset_range _ A_rg A_rg)]
  rcases better_PFR_conjecture (h₀A.preimage' A_rg) hA' with ⟨H', c', hc', hH', hH'₂⟩
  refine ⟨H'.map ι , ι '' c', toFinite _, toFinite (ι '' H'), ?_, ?_, fun x hx ↦ ?_⟩
  · rwa [Nat.card_image_of_injective ι_inj]
  · erw [Nat.card_image_of_injective ι_inj, ← cardA']
    exact hH'
  · erw [← image_add]
    exact ⟨⟨x, Submodule.subset_span hx⟩, hH'₂ hx, rfl⟩
