import PFR.f2_vec
import PFR.ruzsa_distance

/-!
# Entropic version of polynomial Freiman-Ruzsa conjecture

Here we prove the entropic version of the polynomial Freiman-Ruzsa conjecture.

## Main results

* `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$.

-/

variable {Ω_0 Ω'_0 : Type*} [mΩ_0 : MeasurableSpace Ω_0] (μ_0 : Measure Ω_0) [mΩ'_0 : MeasurableSpace Ω'_0] (μ'_0 : Measure Ω'_0)

variable {Ω Ω' Ω'' Ω''' : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [mΩ' : MeasurableSpace Ω'] (μ' : Measure Ω') [mΩ'' : MeasurableSpace Ω''] (μ'' : Measure Ω'') [mΩ''' : MeasurableSpace Ω'''] (μ''' : Measure Ω''')

variable [AddCommGroup G] [ElementaryAddGroup G 2] [Fintype G]

variable (X_0_1: Ω_0 → G) (X_0_2: Ω'_0 → G)
(X_1: Ω → G) (X_2: Ω' → G)

def eta := (9:ℝ)⁻¹

/-- If $X_1,X_2$ are two $G$-valued random variables, then
$$  \tau[X_1; X_2] \coloneqq d[X_1; X_2] + \eta  d[X^0_1; X_1] + \eta d[X^0_2; X_2].$$ --/
def tau (X_1: Ω → G) (X_2 : Ω' → G) : ℝ := sorry

/-- If $X'_1, X'_2$ are copies of $X_1,X_2$, then $\tau[X'_1;X'_2] = \tau[X_1;X_2]$. --/
lemma tau_of_copy : 0 = 1 := sorry

/--  There exist $G$-valued random variables $X_1, X_2$ such that
  $$\tau[X_1;X_2] \leq \tau[X'_1;X'_2]
  $$
for all $G$-valued random variables $X'_1, X'_2$.-/
lemma tau_min_exists : 0 = 1 := sorry




/-- If $d[X_1;X_2] > 0$ then  there are $G$-valued random variables $X'_1, X'_2$ such that
$$ \tau[X'_1;X'_2] < \tau[X_1;X_2].$$ -/
theorem tau_strictly_decreases : 0 = 1 := sorry

/-- `entropic_PFR_conjecture`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 11 d[X^0_1;X^0_2]$. -/
theorem entropic_PFR_conjecture : 0 = 1 := by sorry
