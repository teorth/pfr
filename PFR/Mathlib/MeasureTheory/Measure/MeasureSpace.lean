import Mathlib.MeasureTheory.Measure.MeasureSpace

noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace
open Classical Topology BigOperators Filter ENNReal NNReal Interval MeasureTheory

variable {α β γ δ ι R R' : Type*}

namespace MeasureTheory
namespace Measure

alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl

variable [MeasurableSpace α] {μ : Measure α} {c : ℝ≥0∞}

lemma smul_absolutelyContinuous : c • μ ≪ μ := absolutelyContinuous_of_le_smul le_rfl
