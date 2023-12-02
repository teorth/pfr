import Mathlib.Probability.Independence.Basic
import PFR.Mathlib.Probability.ConditionalProbability

open MeasureTheory

namespace ProbabilityTheory
variable {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] {μ : Measure Ω} {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}

/-- The assertion that `X` and `Y` are conditionally independent relative to `Z`. -/
def condIndepFun (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ z ∂ (μ.map Z), IndepFun X Y (μ[|Z ← z])

lemma condIndepFun_iff : condIndepFun X Y Z μ ↔ ∀ᵐ z ∂ (μ.map Z), IndepFun X Y (μ[|Z ← z]) := by rfl
