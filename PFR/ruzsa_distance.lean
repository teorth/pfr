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

/-- If $X$ is $G$-valued, then $\bbH[-X]=\bbH[X]$. -/
lemma ent_of_neg : 0 = 1 := by sorry

/-- $$ \max(H[X], H[Y]) - I[X:Y] \leq H[X \pm Y].$$ -/
lemma ent_of_sumdiff_lower : 0 = 1 := by sorry

/-- $$ \max(H[X|Z], H[Y|Z]) - I[X:Y|Z] \leq \bbH[X\pm Y|Z] $$ -/
lemma condEnt_of_sumdiff_lower : 0 = 1 := by sorry

/-- $$ \max(H[X], H[Y]) \leq H[X\pm Y].$$ -/
lemma ent_of_indep_sumdiff_lower : 0 = 1 := by sorry



/-- The Ruzsa distance `dist X Y` between two random variables is defined as $H[X'-Y'] - H[X']/2 - H[Y']/2$, where $X',Y'$ are independent copies of $X, Y$. -/
def dist (X : Ω → G) (Y : Ω' → G) : ℝ := sorry

-- may also want to make further notations for Ruzsa distance

/-- If $X',Y'$ are copies of $X,Y$ respectively then $d[X';Y']=d[X;Y]$. -/
lemma dist_of_copy : 0 = 1 := by sorry

/--   If $X,Y$ are independent $G$-random variables then
  $$ d[X;Y] := H[X - Y] - H[X]/2 - H[Y]/2.$$-/
lemma dist_of_indep : 0 = 1 := by sorry

/-- $$ d[X;Y] = d[Y;X].$$ -/
lemma dist_symm : 0 = 1 := by sorry

/-- $$|H[X]-H[Y]| \leq 2 d[X;Y].$$ -/
lemma diff_ent_le_dist : 0 = 1 := by sorry

/-- $$  \bbH[X-Y] - \bbH[X], \bbH[X-Y] - \bbH[Y] \leq 2d[X;Y].$$ -/
lemma diff_ent_le_dist' : 0 = 1 := by sorry

/--   $$ d[X;Y] \geq 0.$$  -/
lemma dist_nonneg : 0 = 1 := by sorry

/-- The Ruzsa triangle inequality -/
lemma Ruzsa_triangle (X : Ω → G) (Y : Ω' → G) (Z : Ω'' → G) : dist X Z ≤ dist X Y + dist Y Z := sorry

/-- definition of d[ X|Z ; Y| W ]-/
def condDist [Fintype S] [Fintype T] (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T) : ℝ := sorry

/-- $$  d[X  | Z;Y | W] = H[X'-Y'|Z',W'] - H[X'|Z']/2 - H[Y'|W']/2$$ -/
lemma condDist_eq : 0 = 1 := by sorry

/-- H[X + Y + Z] - H[X + Y] \leq H[Y+Z] - H[Y]. -/
lemma Kaimonovich_Vershik : 0 = 1 := by sorry

section Balog_Szemeredi_Gowers

/-- If $(X_1,Y'), (X_2,Y')$ are conditionally
independent trials of $X$ relative to $Y$, then
$$ H[X_1,X_2,Y] = 2 H[X] + H[Y] + 2 I[X:Y] = 2 H[X,Y] - H[Y].$$ -/
lemma ent_of_cond_indep : 0 = 1 := by sorry


/--  Let $A,B$ be $G$-valued random variables on $\Omega$, and set $Z \coloneq A+B$.
Then $$ \sum_{z} P[Z=z] d[(A | Z = z); (B | Z = z)] \leq 3 I[A:B] + 2 H[Z] - H[A] - H[B]. $$ -/
lemma ent_bsg : 0 = 1 := by sorry


end
