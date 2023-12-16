import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.SetIntegral

open scoped BigOperators

namespace MeasureTheory
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

-- TODO: Replace `integral_fintype`?
lemma integral_eq_sum (μ : Measure α) [IsFiniteMeasure μ] [MeasurableSingletonClass α] [Fintype α]
    (f : α → E) : ∫ x, f x ∂μ = ∑ x, (μ {x}).toReal • f x :=
  integral_fintype _ $ integrable_of_fintype _ _

-- needs to be golfed
lemma integral_eq_sum_finset (μ : Measure α) [IsFiniteMeasure μ] [MeasurableSingletonClass α] (A : Finset α) (f : α → E) : ∫ x in A, f x ∂μ = ∑ x in A, (μ {x}).toReal • f x := by
  apply integral_finset
  apply IntegrableOn.integrable
  observe : A = ⋃ x ∈ A, {x}
  rw [this, integrableOn_finset_iUnion]
  intro x _
  rw [integrableOn_singleton_iff]
  right; exact measure_lt_top μ {x}

lemma integral_eq_sum_finset' (μ : Measure α) [IsFiniteMeasure μ] [MeasurableSingletonClass α] {A : Finset α} (f : α → E) (hA : μ Aᶜ = 0): ∫ x, f x ∂μ = ∑ x in A, (μ {x}).toReal • f x := by
  have hA' : (A : Set α) =ᵐ[μ] Set.univ := by rwa [MeasureTheory.ae_eq_univ]
  rw [<-integral_univ, <- set_integral_congr_set_ae hA']
  exact integral_eq_sum_finset μ A f

lemma lintegral_eq_sum_finset (μ : Measure α) [IsFiniteMeasure μ] [MeasurableSingletonClass α] (A : Finset α) (f : α → ENNReal) : ∫⁻ x in A, f x ∂μ = ∑ x in A, (f x) * (μ {x}) := by
  apply lintegral_finset

lemma lintegral_eq_sum_finset' (μ : Measure α) [IsFiniteMeasure μ] [MeasurableSingletonClass α] {A : Finset α} (f : α → ENNReal) (hA : μ Aᶜ = 0): ∫⁻ x, f x ∂μ = ∑ x in A, (f x) * (μ {x}) := by
  have hA' : (A : Set α) =ᵐ[μ] Set.univ := by rwa [MeasureTheory.ae_eq_univ]
  rw [<-MeasureTheory.set_lintegral_univ,  <-MeasureTheory.set_lintegral_congr hA']
  exact lintegral_eq_sum_finset μ A f

lemma lintegral_eq_single  (μ : Measure α) [IsFiniteMeasure μ] [MeasurableSingletonClass α] (a : α) (f : α → ENNReal) (ha : ∀ b : α, b ≠ a → f b = 0) : ∫⁻ x, f x ∂μ = f a * μ {a} := by
  rw [<- lintegral_add_compl f (A := {a}) (MeasurableSet.singleton a), lintegral_singleton]
  convert add_zero _
  rw [set_lintegral_congr_fun (g := fun _ ↦ 0) (MeasurableSet.compl (MeasurableSet.singleton a))]
  . exact lintegral_zero
  apply ae_of_all
  intro b hb
  simp at hb
  exact ha b hb


end MeasureTheory
