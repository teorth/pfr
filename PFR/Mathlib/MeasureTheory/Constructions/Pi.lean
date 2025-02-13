import Mathlib.MeasureTheory.Constructions.Pi

open Function Set

namespace MeasureTheory.Measure
variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

instance : IsProbabilityMeasure (.pi μ) :=
  ⟨by simp_rw [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[simp]
lemma pi_pi_set (t : Set ι) [DecidablePred (· ∈ t)] (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi t s) = ∏ i ∈ Finset.univ.filter (· ∈ t), μ i (s i) := by
  classical
  simp (config := {singlePass := true}) only [← pi_univ_ite]
  simp_rw [pi_pi, apply_ite, measure_univ,
    Finset.prod_ite, Finset.prod_const_one, mul_one]

@[simp]
lemma pi_pi_finset (t : Finset ι) (s : ∀ i, Set (α i)) :
    Measure.pi μ (pi t s) = ∏ i ∈ t, μ i (s i) := by
  classical
  rw [pi_pi_set]
  congr; ext x; simp

@[simp]
lemma pi_eval_preimage (i : ι) (s : Set (α i)) :
    Measure.pi μ (eval i ⁻¹' s) = μ i s := by
  classical
  simp_rw [eval_preimage, pi_pi, apply_update (fun i ↦ μ i), measure_univ,
    Finset.prod_update_of_mem (Finset.mem_univ _), Finset.prod_const_one, mul_one]

lemma map_eval_pi (i : ι) : Measure.map (eval i) (Measure.pi μ) = μ i := by
  ext s hs
  simp_rw [Measure.map_apply (measurable_pi_apply i) hs, pi_eval_preimage]
