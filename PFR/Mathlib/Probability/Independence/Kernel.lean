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
