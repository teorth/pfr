import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Products of finite measures and probability measures
-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section pi

namespace ProbabilityMeasure

variable {ι : Type*} {α : ι → Type*} [Fintype ι]

variable [∀ i, MeasurableSpace (α i)]

/-- The product of finitely many probability measure, as a `ProbabilityMeasure`. -/
noncomputable def pi (μ : Π i, ProbabilityMeasure (α i)) : ProbabilityMeasure (Π i, α i) :=
  ⟨Measure.pi (fun i ↦ μ i), by infer_instance⟩

lemma pi_singleton {μ : Π i, ProbabilityMeasure (α i)} {x : Π i, α i} :
    ProbabilityMeasure.pi μ {x} = ∏ i, μ i {x i} := by
  simp only [pi, ← univ_pi_singleton x, mk_apply, Measure.pi_pi, toNNReal_prod]
  rfl

variable [∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)] [∀ i, Fintype (α i)]
  [∀ i, DiscreteTopology (α i)]

/-- The assumptions in this proof are way too strong (this would work in any metrizable
second-countable space), but enough for our application. -/
lemma continuous_pi :
    Continuous (fun (μ : Π i, ProbabilityMeasure (α i)) ↦ ProbabilityMeasure.pi μ) := by
  apply continuous_iff_seqContinuous.2
  intro u μ hu
  have A (x : Π i, α i) : Tendsto (fun (μ : Π i, ProbabilityMeasure (α i)) ↦ pi μ {x})
      (𝓝 μ) (𝓝 (pi μ {x})) := by
    simp [pi_singleton]
    apply tendsto_finset_prod
    intro i hi
    have : Tendsto (fun (b : ProbabilityMeasure (α i)) ↦ b {x i}) (𝓝 (μ i)) (𝓝 (μ i {x i})) := by
      letI : MetricSpace (α i) := TopologicalSpace.metrizableSpaceMetric (α i)
      apply ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto tendsto_id
      simp
    apply Tendsto.comp this
    exact Tendsto.apply_nhds (fun ⦃U⦄ a ↦ a) i
  have B (s : Finset (Π i, α i)) : Tendsto (fun (μ : Π i, ProbabilityMeasure (α i)) ↦ pi μ s)
      (𝓝 μ) (𝓝 (pi μ s)) := by
    have C (ν : ProbabilityMeasure (Π i, α i)) : ν s = ∑ x ∈ s, ν {x} := by
      simp only [ProbabilityMeasure.coeFn_def]
      rw [← sum_measure_singleton, toNNReal_sum]
      simp
    simp only [C]
    exact tendsto_finset_sum _ (fun i hi ↦ A _)
  have C (s : Set (Π i, α i)) : Tendsto (fun (μ : Π i, ProbabilityMeasure (α i)) ↦ pi μ s)
      (𝓝 μ) (𝓝 (pi μ s)) := by
    classical
    let s' := s.toFinset
    convert B s' <;> simp [s']
  simp only
  apply tendsto_of_forall_isOpen_le_liminf (fun s hs ↦ ?_)
  exact ((C s).comp hu).liminf_eq.symm.le

end ProbabilityMeasure

end pi

end MeasureTheory -- namespace
