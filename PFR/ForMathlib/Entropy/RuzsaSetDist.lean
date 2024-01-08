import Mathlib.Data.ENat.Basic
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Card
import PFR.ForMathlib.Entropy.Basic
import PFR.ForMathlib.Entropy.RuzsaDist
import PFR.ForMathlib.MeasureReal
import PFR.ForMathlib.Uniform


section UniformMeasure

/- Here we set up the foundational theory of discrete uniform measures on finite non-empty sets. -/

open BigOperators

namespace MeasureTheory.Measure

variable {S : Type*} [MeasurableSpace S] (H : Set S)

/-- In practice one would also impose the conditions `MeasurableSingletonClass S`, `Finite H` and `Nonempty H` before attempting to use this definition. -/
noncomputable def discreteUniform : Measure S := ((Set.encard H).toENNReal)⁻¹ • (restrict count H)

/-- The uniform distribution on an infinite set vanishes by definition. -/
lemma discreteUniform_of_infinite (h: Set.Infinite H) : discreteUniform H = 0 := by
  simp [discreteUniform, Set.Infinite.encard_eq h]

variable [MeasurableSingletonClass S] [Finite H]

/-- The usual formula for the discrete uniform measure applied to an arbitrary set. -/
lemma discreteUniform_apply (A : Set S) :
  discreteUniform H A = (Nat.card (A ∩ H : Set S)) / Nat.card H := by
    have : Fintype (A ∩ H : Set S) := Fintype.ofFinite (A ∩ H : Set S)

    rw [discreteUniform, smul_apply, restrict_apply' (Set.Finite.measurableSet H.toFinite), count_apply (Set.Finite.measurableSet (A ∩ H).toFinite), tsum_eq_sum (s := Finset.univ)]
    . simp [Finset.card_univ, ENNReal.div_eq_inv_mul, Set.Nat.card_coe_set_eq, Set.ncard_def]
      congr
      rw [<-ENat.coe_toNat (n := Set.encard H) _]
      . rfl
      simp [H.toFinite]
    simp

/-- Variant of `discreteUniform_apply' using real-valued measures. -/
lemma discreteUniform_apply' (A : Set S) :
  (discreteUniform H).real A = (Nat.card (A ∩ H : Set S)) / Nat.card H := by
  rw [measureReal_def, discreteUniform_apply, ENNReal.toReal_div]
  congr

variable [Nonempty H]

instance discreteUniform.isProbabilityMeasure  : IsProbabilityMeasure (discreteUniform H) := by
  rw [isProbabilityMeasure_iff, discreteUniform_apply, Set.univ_inter, ENNReal.div_self]
  . simp [Nat.pos_iff_ne_zero.mp Nat.card_pos]
  simp

/--  injective map of discrete uniform is discrete uniform -/
lemma map_discreteUniform_of_inj {T: Type*} [MeasurableSpace T] [MeasurableSingletonClass T] {f : S → T} (hmes : Measurable f) (hf : Function.Injective f) : (discreteUniform H).map f = discreteUniform (f '' H) := by
  ext A hA
  simp_rw [map_apply hmes hA, discreteUniform_apply, Nat.card_image_of_injective hf, Set.Nat.card_coe_set_eq, <-Set.ncard_image_of_injective (f⁻¹' A ∩ H) hf]
  congr; ext t; simp
  constructor
  . rintro ⟨ s, ⟨ hs, hs' ⟩, hs'' ⟩
    exact ⟨ hs'' ▸ hs, ⟨ s, hs', hs'' ⟩ ⟩
  rintro ⟨ ht, s, ⟨ hs, hs'⟩ ⟩
  exact ⟨ s, ⟨ hs' ▸ ht, hs ⟩, hs' ⟩

/-- A random variable is uniform iff its distribution is. -/
lemma isUniform_iff_uniform_dist {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ: Measure Ω} [Countable S] (hμ: IsProbabilityMeasure μ) {U: Ω → S} (hU: Measurable U) :
  ProbabilityTheory.IsUniform H U μ ↔ μ.map U = discreteUniform H := by
  constructor
  . intro h_unif
    ext A hA
    let Hf := H.toFinite.toFinset
    have h_unif': ProbabilityTheory.IsUniform Hf U μ := (Set.Finite.coe_toFinset H.toFinite).symm ▸ h_unif
    let AHf := (A ∩ H).toFinite.toFinset

    rw [discreteUniform_apply, <-MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hA]
    classical
    calc ∑' x, Set.indicator A (fun x => (μ.map U) {x}) x
      _ = ∑' x, (if x ∈ (A ∩ H) then (1:ENNReal) / (Nat.card H) else 0) := by
        congr with x
        by_cases h : x ∈ A
        . by_cases h' : x ∈ H
          . simp [h, h', map_apply hU (MeasurableSet.singleton x), ProbabilityTheory.IsUniform.measure_preimage_of_mem h_unif' hU ((Set.Finite.coe_toFinset H.toFinite).symm ▸ h')]
          simp [h, h', map_apply hU (MeasurableSet.singleton x), ProbabilityTheory.IsUniform.measure_preimage_of_nmem h_unif' ((Set.Finite.coe_toFinset H.toFinite).symm ▸ h')]
        simp [h]
      _ = Finset.sum AHf (fun _ ↦ (1:ENNReal) / (Nat.card H)) := by
        rw [tsum_eq_sum (s := (A ∩ H).toFinite.toFinset)]
        . apply Finset.sum_congr (by rfl)
          intro x hx
          simp at hx
          simp [hx]
        intro x hx
        simp at hx
        simpa
      _ = (Nat.card (A ∩ H:Set S)) / (Nat.card H) := by
        simp [Finset.sum_const, <-Set.ncard_eq_toFinset_card (A ∩ H), Set.Nat.card_coe_set_eq]
        rfl
  intro this
  constructor
  . intro x y hx hy
    replace hx : {x} ∩ H = {x} := by simp [hx]
    replace hy : {y} ∩ H = {y} := by simp [hy]
    simp [<-map_apply hU (MeasurableSet.singleton _), this, discreteUniform_apply, hx, hy]
  rw [<-map_apply hU (by measurability), this, discreteUniform_apply]
  simp

open Real ProbabilityTheory

/-- The entropy of a uniform measure is the log of the cardinality of its support. -/
lemma _root_.ProbabilityTheory.entropy_of_discreteUniform : measureEntropy (discreteUniform H) = log (Nat.card H) := by
  simp [measureEntropy_def', discreteUniform_apply']
  classical
  calc ∑' s, negMulLog ((Nat.card ({s} ∩ H : Set S)) / (Nat.card H))
    _ = ∑' s, if s ∈ H then negMulLog (1 / (Nat.card H)) else 0 := by
      congr with s
      by_cases h: s ∈ H
      all_goals simp [h]
    _ = ∑ s in H.toFinite.toFinset, negMulLog (1 / (Nat.card H)) := by
      convert tsum_eq_sum (s := H.toFinite.toFinset) ?_ using 2 with s hs
      . simp at hs; simp [hs]
      intro s hs
      simp at hs; simp [hs]
    _ = (Nat.card H) * negMulLog (1 / (Nat.card H)) := by
      simp [<-Set.ncard_coe_Finset, Set.Nat.card_coe_set_eq]
    _ = log (Nat.card H) := by
      simp [negMulLog, Nat.card_pos, <-mul_assoc]
      rw [mul_inv_cancel, one_mul]
      simp only [ne_eq, Nat.cast_eq_zero, Nat.card_ne_zero]
      exact ⟨ ‹_›, ‹_› ⟩

end MeasureTheory.Measure

end UniformMeasure

section RuzsaSetDist

namespace ProbabilityTheory

open MeasureTheory Pointwise Real

variable {G:Type*} [Countable G]  [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

/-- The Ruzsa distance between two subsets `A`, `B` of a group `G` is defined to be the Ruzsa distance between their uniform probability distributions.  Is only intended for use when `A`, `B` are finite and non-empty. -/
noncomputable def rdist_set (A B: Set G) : ℝ := kernel.rdistm (Measure.discreteUniform A) (Measure.discreteUniform B)

notation3:max "dᵤ[" A " # " B "]" => rdist_set A B

/-- Relating Ruzsa distance between sets to Ruzsa distance between random variables -/
lemma rdist_set_eq_rdist {A B: Set G} [Finite A] [Finite B]  [Nonempty A] [Nonempty B] {Ω Ω': Type*} [mΩ : MeasureSpace Ω] [mΩ' : MeasureSpace Ω'] (hμ: IsProbabilityMeasure (ℙ: Measure Ω)) (hμ': IsProbabilityMeasure (ℙ: Measure Ω')) {UA: Ω → G} {UB: Ω' → G} (hUA : IsUniform A UA ℙ) (hUB : IsUniform B UB ℙ) (hUA_mes : Measurable UA) (hUB_mes : Measurable UB) : dᵤ[A # B] = d[UA # UB] := by
  rw [rdist_eq_rdistm, rdist_set, (Measure.isUniform_iff_uniform_dist A hμ hUA_mes).mp hUA, (Measure.isUniform_iff_uniform_dist B hμ' hUB_mes).mp hUB]

/-- Ruzsa distance between sets is nonnegative. -/
lemma rdist_set_nonneg (A B: Set G) [Finite A] [Finite B]  [Nonempty A] [Nonempty B] : 0 ≤ dᵤ[A # B] := by
  obtain ⟨ Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, UA_hfin ⟩ := exists_isUniform_measureSpace' A
  obtain ⟨ Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, UB_hfin ⟩ := exists_isUniform_measureSpace' B
  rw [rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes]
  exact rdist_nonneg hUA_mes hUB_mes

/-- Ruzsa distance between sets is symmetric. -/
lemma rdist_set_symm (A B: Set G) [Finite A] [Finite B]  [Nonempty A] [Nonempty B] : dᵤ[A # B] = dᵤ[B # A] := by
  obtain ⟨ Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, - ⟩ := exists_isUniform_measureSpace' A
  obtain ⟨ Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, - ⟩ := exists_isUniform_measureSpace' B
  rw [rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes, rdist_set_eq_rdist hμ' hμ hUB_unif hUA_unif hUB_mes hUA_mes]
  exact rdist_symm

/-- Ruzsa distance between sets obeys the triangle inequality. -/
lemma rdist_set_triangle (A B C: Set G) [Finite A] [Finite B] [Finite C] [Nonempty A] [Nonempty B] [Nonempty C] : dᵤ[A # C] ≤ dᵤ[A # B] + dᵤ[B # C] := by
  obtain ⟨ Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, hUA_fin ⟩ := exists_isUniform_measureSpace' A
  obtain ⟨ Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, hUB_fin ⟩ := exists_isUniform_measureSpace' B
  obtain ⟨ Ω'', mΩ'', UC, hμ'', hUC_mes, hUC_unif, -, hUC_fin ⟩ := exists_isUniform_measureSpace' C
  rw [rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes, rdist_set_eq_rdist hμ' hμ'' hUB_unif hUC_unif hUB_mes hUC_mes, rdist_set_eq_rdist hμ hμ'' hUA_unif hUC_unif hUA_mes hUC_mes]
  exact rdist_triangle hUA_mes hUB_mes hUC_mes

/-- Ruzsa distance between sets is translation invariant. -/
lemma rdist_set_add_const (A B: Set G) [Finite A] [Finite B]  [Nonempty A] [Nonempty B] (c c' : G) : dᵤ[A + {c} # B + {c'}] = dᵤ[A # B] := by
  obtain ⟨ Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, hUA_fin ⟩ := exists_isUniform_measureSpace' A
  obtain ⟨ Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, hUB_fin ⟩ := exists_isUniform_measureSpace' B
  rw [rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes, <- rdist_add_const' c c' hUA_mes hUB_mes]
  classical
  convert rdist_set_eq_rdist (A := A+{c}) (B := B+{c'}) hμ hμ' ?_ ?_ ?_ ?_
  . exact Set.Nonempty.to_subtype (Set.Nonempty.add (Set.nonempty_coe_sort.mp ‹_›) (Set.singleton_nonempty _))
  . exact Set.Nonempty.to_subtype (Set.Nonempty.add (Set.nonempty_coe_sort.mp ‹_›) (Set.singleton_nonempty _))
  . convert IsUniform.comp (A.toFinite.coe_toFinset.symm ▸ hUA_unif) (add_left_injective c) using 1
    simp
  . convert IsUniform.comp (B.toFinite.coe_toFinset.symm ▸ hUB_unif) (add_left_injective c') using 1
    simp
  . measurability
  measurability

/-- Ruzsa distance between sets is preserved by injective homomorphisms. -/
lemma rdist_set_of_inj (A B: Set G) [Finite A] [Finite B]  [Nonempty A] [Nonempty B] {H:Type*} [hH : MeasurableSpace H] [MeasurableSingletonClass H] [AddCommGroup H]
 [Countable H] {φ: G →+ H} (hφ: Function.Injective φ) : dᵤ[φ '' A # φ '' B] = dᵤ[A # B] := by
  obtain ⟨ Ω, mΩ, UA, hμ, hUA_mes, hUA_unif, -, - ⟩ := exists_isUniform_measureSpace' A
  obtain ⟨ Ω', mΩ', UB, hμ', hUB_mes, hUB_unif, -, - ⟩ := exists_isUniform_measureSpace' B
  rw [rdist_set_eq_rdist hμ hμ' hUA_unif hUB_unif hUA_mes hUB_mes, <-rdist_of_inj hUA_mes hUB_mes φ hφ]
  classical
  convert rdist_set_eq_rdist (A := φ '' A) (B := φ '' B) hμ hμ' ?_ ?_ ?_ ?_
  . convert IsUniform.comp (A.toFinite.coe_toFinset.symm ▸ hUA_unif) hφ using 1
    ext x; simp
  . convert IsUniform.comp (B.toFinite.coe_toFinset.symm ▸ hUB_unif) hφ using 1
    ext x; simp
  . measurability
  measurability

/-- Ruzsa distance between sets is controlled by the doubling constant. -/
lemma rdist_set_le (A B: Set G) [Finite A] [Finite B] (hA : A.Nonempty) (hB : B.Nonempty) :
    dᵤ[A # B] ≤ log (Nat.card (A-B)) - log (Nat.card A) / 2 - log (Nat.card B) / 2 := by
  have := hA.to_subtype
  have := hB.to_subtype
  simp_rw [rdist_set, kernel.rdistm, ProbabilityTheory.entropy_of_discreteUniform]
  gcongr
  convert measureEntropy_le_card_aux (A-B).toFinite.toFinset ?_
  . rw [Set.Nat.card_coe_set_eq,]
    exact Set.ncard_eq_toFinset_card (A - B)
  . exact isProbabilityMeasure_map (Measurable.aemeasurable measurable_sub)
  rw [Measure.map_apply measurable_sub (measurableSet_discrete _)]
  apply MeasureTheory.measure_mono_null (s₂ := (Aᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Bᶜ))
  . intro (x, y)
    contrapose!
    aesop (add unsafe Set.sub_mem_sub, simp not_or)
  apply MeasureTheory.measure_union_null
  all_goals simp [Measure.discreteUniform_apply]

end ProbabilityTheory
end RuzsaSetDist
