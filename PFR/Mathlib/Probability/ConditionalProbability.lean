import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic

/-!
## TODO

Less explicit arguments to `cond_eq_zero_of_meas_eq_zero`
-/

open MeasureTheory Measure Set

namespace ProbabilityTheory

variable {ι Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {X : ι → Ω → α} {Y : ι → Ω → β} {f : _ → Set Ω}
  {t : ι → Set β} {s : Finset ι}

lemma ae_cond_mem {s : Set Ω} (hs : MeasurableSet s) : ∀ᵐ x ∂μ[|s], x ∈ s :=
  ae_smul_measure (ae_restrict_mem hs) _

/-- The probability of an intersection of preimaαes conditioninα on another intersection factors
into a product. -/
lemma cond_iInter [Finite ι] (hY : ∀ i, Measurable (Y i))
    (h_indep : iIndepFun (fun _ ↦ mα.prod mβ) (fun i ω ↦ (X i ω, Y i ω)) μ)
    (hf : ∀ i ∈ s, MeasurableSet[mα.comap (X i)] (f i))
    (hy : ∀ i, μ (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
    μ[|⋂ i, Y i ⁻¹' t i] (⋂ i ∈ s, f i) = ∏ i ∈ s, μ[|Y i ⁻¹' t i] (f i) := by
  have : IsProbabilityMeasure (μ : Measure Ω) := h_indep.isProbabilityMeasure
  classical
  cases nonempty_fintype ι
  let g (i' : ι) := if i' ∈ s then Y i' ⁻¹' t i' ∩ f i' else Y i' ⁻¹' t i'

  calc
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ ((⋂ i, Y i ⁻¹' t i) ∩ ⋂ i ∈ s, f i) := by
      rw [cond_apply]; exact .iInter fun i ↦ hY i (ht i)
    _ = (μ (⋂ i, Y i ⁻¹' t i))⁻¹ * μ (⋂ i, g i) := by
      congr
      calc
        _ = (⋂ i, Y i ⁻¹' t i) ∩ ⋂ i, if i ∈ s then f i else Set.univ := by
          congr
          simp only [Set.iInter_ite, Set.iInter_univ, Set.inter_univ]
        _ = ⋂ i, Y i ⁻¹' t i ∩ (if i ∈ s then f i else Set.univ) := by rw [Set.iInter_inter_distrib]
        _ = _ := Set.iInter_congr fun i ↦ by by_cases hi : i ∈ s <;> simp [hi, g]
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * μ (⋂ i, g i) := by
      rw [iIndepFun.meas_iInter h_indep]
      exact fun i ↦ ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp [eq_comm]⟩
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * ∏ i, μ (g i) := by
      rw [iIndepFun.meas_iInter h_indep]
      intro i
      by_cases hi : i ∈ s
      . simp only [hi, ↓reduceIte, g]
        obtain ⟨A, hA, hA'⟩ := hf i hi
        exact .inter ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp [eq_comm]⟩
          ⟨A ×ˢ Set.univ, hA.prod .univ, by ext; simp [← hA']⟩
      simp only [hi, ↓reduceIte, g]
      exact ⟨.univ ×ˢ t i, MeasurableSet.univ.prod (ht _), by ext; simp [eq_comm]⟩
    _ = (∏ i, μ (Y i ⁻¹' t i))⁻¹ * ∏ i, (μ (Y i ⁻¹' t i)) * ((μ (Y i ⁻¹' t i))⁻¹ * μ (g i)) := by
      congr
      ext i
      rw [← mul_assoc, ENNReal.mul_inv_cancel (hy i) (measure_ne_top μ _), one_mul]
    _ = ∏ i, (μ (Y i ⁻¹' t i))⁻¹ * μ (g i) := by
      rw [Finset.prod_mul_distrib, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
      . exact Finset.prod_ne_zero_iff.mpr fun a _ ↦ hy a
      · exact ENNReal.prod_ne_top fun _ _ ↦ measure_ne_top _ _
    _ = ∏ i, if i ∈ s then μ[|Y i ⁻¹' t i] (f i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i ∈ s
      . simp only [h, ↓reduceIte, g, cond_apply (hY i (ht i))]
      · simp only [h, ↓reduceIte, g, ENNReal.inv_mul_cancel (hy i) (measure_ne_top μ _)]
    _ = _ := by simp

lemma iIndepFun.cond [Finite ι] (hY : ∀ i, Measurable (Y i))
    (h_indep : iIndepFun (fun _ ↦ mα.prod mβ) (fun i ω ↦ (X i ω, Y i ω)) μ)
    (hy : ∀ i, μ (Y i ⁻¹' t i) ≠ 0) (ht : ∀ i, MeasurableSet (t i)) :
    iIndepFun (fun _ ↦ mα) X μ[|⋂ i, Y i ⁻¹' t i] := by
  rw [iIndepFun_iff]
  intro s f' hf'
  have h1 : ∀ i : s, μ[|⋂ i, Y i ⁻¹' t i] (f' i) = μ[|Y i ⁻¹' t i] (f' i) := by
    intro i
    let s' : Finset ι := {i.val}
    have hs' : s' ⊆ s := by
      simp only [Finset.singleton_subset_iff, Finset.coe_mem, s']
    have h := cond_iInter hY h_indep (fun i hi ↦ hf' _ <| hs' hi) hy ht
    simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, Finset.prod_singleton, s'] at h
    exact h
  rw [cond_iInter hY h_indep hf' hy ht]
  apply Finset.prod_congr rfl
  intro i hi
  exact (h1 ⟨i, hi⟩).symm

end ProbabilityTheory
