import Mathlib.Probability.Notation
import Mathlib.Probability.ConditionalProbability
import PFR.entropy_basic

/-!
# Ruzsa distance

Here we define Ruzsa distance and establish its basic properties.

## Main definitions

* `dist`: The Ruzsa distance between two random variables

## Main results

* `Ruzsa_triangle`: The Ruzsa triangle inequality for three random variables.

-/
open MeasureTheory

variable {Ω Ω' Ω'' G : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'} [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''} [AddCommGroup G] [Fintype G]

-- may also want [DecidableEq G]

/-- The Ruzsa distance `dist X Y` between two random variables is defined as $H[X'-Y'] - H[X']/2 - H[Y']/2$, where $X',Y'$ are independent copies of $X, Y$. -/
def dist (X : Ω → G) (Y : Ω' → G) : ℝ := sorry

/-- The Ruzsa triangle inequality -/
lemma Ruzsa_triangle (X : Ω → G) (Y : Ω' → G) (Z : Ω'' → G) : dist X Z ≤ dist X Y + dist Y Z := sorry

-- will eventually also need conditional versions of Ruzsa distance
