import Mathlib.Probability.Independence.Kernel

section IndepFun

/-! ### Independence of random variables

-/

open MeasureTheory

namespace ProbabilityTheory.kernel

variable {β β' γ γ' : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}

@[to_additive]
lemma iIndepFun.mul_left [IsMarkovKernel κ] {ι : Type*} {β : Type*} {m : MeasurableSpace β}
    [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : iIndepFun (fun _ => m) f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) κ μ := by
  have : IndepFun (fun ω => (f i ω, f j ω)) (f k) κ μ :=
    hf_Indep.indepFun_prod hf_meas i j k hik hjk
  change IndepFun ((fun p : β × β => p.fst * p.snd) ∘ fun ω => (f i ω, f j ω)) (id ∘ f k) κ μ
  exact IndepFun.comp this (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
lemma iIndepFun.mul_right [IsMarkovKernel κ] {ι : Type*} {β : Type*} {m : MeasurableSpace β}
    [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : iIndepFun (fun _ => m) f κ μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) κ μ :=
  (hf_Indep.mul_left hf_meas _ _ _ hij.symm hik.symm).symm

/-- Improved version of `IndepFun.ae_eq` in which the ranges are allowed to be distinct. Perhaps can serve as a replacement of that method? -/
theorem IndepFun.ae_eq' {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}  {f f' : Ω → β} {g g' : Ω → β'} (hfg : IndepFun f g κ μ)
    (hf : ∀ᵐ a ∂μ, f =ᵐ[κ a] f') (hg : ∀ᵐ a ∂μ, g =ᵐ[κ a] g') :
    IndepFun f' g' κ μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg'
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp B
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]
