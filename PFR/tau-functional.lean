import PFR.f2_vec
import PFR.ruzsa_distance

/-!
# The tau functional

Definition of the tau functional and basic facts

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

/-- The property that
  $$\tau[X_1;X_2] \leq \tau[X'_1;X'_2]
  $$
for all $G$-valued random variables $X'_1, X'_2$.  --/
def tau_minimizes (X_1: Ω → G) (X_2 : Ω' → G) : Prop := sorry

/--  There exist $G$-valued random variables $X_1, X_2$ such that tau_minimizes holds.
-/
lemma tau_min_exists : 0 = 1 := sorry

/-- If $X_1,X_2$ are tau-minimizers with $d[X_1,X_2]=k$, then
$$ d[X'_1;X'_2] \geq k - \eta (d[X^0_1;X'_1] - d[X^0_1;X_1] ) - - \eta (d[X^0_2;X'_2] - d[X^0_2;X_2] )$$
for any $G$-valued random variables $X'_1,X'_2$.
-/
lemma distance_ge_of_min : 0 = 1 := sorry

/--   For any $G$-valued random variables $X'_1,X'_2$ and random variables $Z,W$, one has
$$ d[X'_1|Z;X'_2|W] \geq k - \eta (d[X^0_1;X'_1|Z] - d[X^0_1;X_1] ) - - \eta (d[X^0_2;X'_2|W] - d[X^0_2;X_2] ).$$
-/
lemma condDistance_ge_of_min : 0 = 1 := sorry
