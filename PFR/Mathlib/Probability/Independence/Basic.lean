import Mathlib.Probability.Independence.Basic
import PFR.Mathlib.Probability.Independence.Kernel

open MeasureTheory MeasurableSpace Set
open scoped BigOperators MeasureTheory ENNReal

namespace ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}

section IndepFun
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

@[to_additive]
lemma iIndepFun.mul_left [IsProbabilityMeasure μ] {ι : Type*} {β : Type*} {m : MeasurableSpace β}
    [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : iIndepFun (fun _ => m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    IndepFun (f i * f j) (f k) μ :=
  kernel.iIndepFun.mul_left hf_Indep hf_meas i j k hik hjk

@[to_additive]
lemma iIndepFun.mul_right [IsProbabilityMeasure μ] {ι : Type*} {β : Type*} {m : MeasurableSpace β}
    [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : iIndepFun (fun _ => m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    IndepFun (f i) (f j * f k) μ :=
  kernel.iIndepFun.mul_right hf_Indep hf_meas i j k hij hik
