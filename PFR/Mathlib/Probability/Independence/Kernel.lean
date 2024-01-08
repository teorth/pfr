import Mathlib.Probability.Independence.Kernel

open MeasureTheory

namespace ProbabilityTheory.kernel
variable {β β' γ γ' : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}


/-- in mathlib as of `4d385393cd569f08ac30425ef886a57bb10daaa5` (TODO: bump) -/
theorem IndepFun.ae_eq' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {f f' : Ω → β}
    {g g' : Ω → β'} (hfg : IndepFun f g κ μ) (hf : ∀ᵐ a ∂μ, f =ᵐ[κ a] f')
    (hg : ∀ᵐ a ∂μ, g =ᵐ[κ a] g') : IndepFun f' g' κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp B
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]
