import Mathlib.Probability.Notation
import Mathlib.Probability.ConditionalProbability
import PFR.entropy_basic

/-!
# Ruzsa distance

Here we define Ruzsa distance and establish its basic properties.

## Main definitions

* `rdist`: The Ruzsa distance between two random variables

## Main results

* `rdist_triangle`: The Ruzsa triangle inequality for three random variables.

-/
open MeasureTheory ProbabilityTheory

variable {Ω Ω' Ω'' Ω''' G T : Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G] [MeasurableSub₂ G] [Fintype G] [MeasurableSpace T]

variable {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}

-- may also want [DecidableEq G]

/-- If $X$ is $G$-valued, then $\bbH[-X]=\bbH[X]$. -/
lemma entropy_neg (hX : Measurable X) : H[-X ; μ] = H[X ; μ] :=
  entropy_comp_of_injective μ hX (fun x ↦ - x) neg_injective

/-- $$ \max(H[X], H[Y]) - I[X:Y] \leq H[X + Y].$$ -/
lemma ent_of_sum_lower {X : Ω → G} {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) : (max H[X; μ] H[Y; μ]) - I[ X : Y; μ] ≤ H[X + Y; μ]  := by sorry

/-- $$ \max(H[X], H[Y]) - I[X:Y] \leq H[X - Y].$$ -/
lemma ent_of_diff_lower {X : Ω → G} {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) : (max H[X; μ] H[Y; μ]) - I[ X : Y; μ] ≤ H[X - Y; μ]  := by sorry

/-- $$ \max(H[X|Z], H[Y|Z]) - I[X:Y|Z] \leq \bbH[X+ Y|Z] $$ -/
lemma condEnt_of_sum_lower {X : Ω → G} {Y : Ω → G} {Z : Ω → T} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) : (max H[ X | Z; μ] H[Y | Z; μ]) - I[ X : Y | Z ; μ] ≤ H[X + Y | Z; μ] := by sorry

/-- $$ \max(H[X|Z], H[Y|Z]) - I[X:Y|Z] \leq \bbH[X - Y|Z] $$ -/
lemma condEnt_of_diff_lower {X : Ω → G} {Y : Ω → G} {Z : Ω → T} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) : (max H[ X | Z; μ] H[Y | Z; μ]) - I[ X : Y | Z ; μ] ≤ H[X - Y | Z; μ] := by sorry

/-- If $X,Y$ are independent, then
$$ \max(H[X], H[Y]) \leq H[X + Y].$$ -/
lemma ent_of_indep_sum_lower  {X : Ω → G} {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y μ) : (max H[X; μ] H[Y; μ])  ≤ H[X + Y; μ]  := by sorry

/--  If $X,Y$ are independent, then
$$ \max(H[X], H[Y]) \leq H[X - Y].$$ -/
lemma ent_of_indep_diff_lower  {X : Ω → G} {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y μ) : (max H[X; μ] H[Y; μ])  ≤ H[X - Y; μ]  := by sorry


/-- The Ruzsa distance `dist X Y` between two random variables is defined as
$H[X'-Y'] - H[X']/2 - H[Y']/2$, where $X',Y'$ are independent copies of $X, Y$. -/
noncomputable
def rdist (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  H[fun x ↦ x.1 - x.2 ; (μ.map X).prod (μ'.map Y)] - H[X ; μ]/2 - H[Y ; μ']/2

/-- Needed a new separator here, chose `#` arbitrarily, but am open to other suggestions -/
notation3:max "d[" X " ; " μ " # " Y " ; " μ' "]" => rdist X Y μ μ'


lemma rdist_def (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω) (μ' : Measure Ω') :
    d[ X ; μ # Y ; μ' ]
      = H[fun x ↦ x.1 - x.2 ; (μ.map X).prod (μ'.map Y)] - H[X ; μ]/2 - H[Y ; μ']/2 := rfl

-- may also want to make further notations for Ruzsa distance

/-- If $X',Y'$ are copies of $X,Y$ respectively then $d[X';Y']=d[X;Y]$. -/
lemma rdist_of_copy {X' : Ω'' → G} {Y' : Ω''' →G} (hX : isCopy X X' μ μ'') (hY : isCopy Y Y' μ' μ''') : d[ X ; μ # Y ; μ' ] = d[ X' ; μ'' # Y' ; μ'''] := by sorry

/--   If $X,Y$ are independent $G$-random variables then
  $$ d[X;Y] := H[X - Y] - H[X]/2 - H[Y]/2.$$-/
lemma rdist_of_indep [IsFiniteMeasure μ] {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y μ) :
    d[ X ; μ # Y ; μ] = H[fun ω ↦ X ω - Y ω ; μ] - H[X ; μ]/2 - H[Y ; μ]/2 := by
  rw [rdist_def]
  congr 2
  have h_prod : (μ.map X).prod (μ.map Y) = μ.map (⟨ X, Y ⟩) :=
    ((indepFun_iff_map_prod_eq_prod_map_map hX hY).mp h).symm
  rw [h_prod, entropy_def, Measure.map_map (measurable_fst.sub measurable_snd) (hX.prod_mk hY)]
  congr

/-- $$ d[X;Y] = d[Y;X].$$ -/
lemma rdist_symm [IsFiniteMeasure μ] [IsFiniteMeasure μ'] : d[ X ; μ # Y ; μ'] = d[ Y ; μ' # X ; μ] := by
  rw [rdist_def, rdist_def, sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_neg (measurable_fst.sub measurable_snd)]
  have : (-fun x : G × G ↦ x.1 - x.2) = (fun x ↦ x.1 - x.2) ∘ Prod.swap := by ext; simp
  rw [this, entropy_def, ← Measure.map_map (measurable_fst.sub measurable_snd) measurable_swap,
    Measure.prod_swap]
  rfl

/-- $$|H[X]-H[Y]| \leq 2 d[X;Y].$$ -/
lemma diff_ent_le_rdist : |H[X ; μ] - H[Y ; μ']| ≤ 2 * d[X ; μ # Y ; μ' ] := by sorry

/-- $$  \bbH[X-Y] - \bbH[X] \leq 2d[X;Y].$$ -/
lemma diff_ent_le_rdist' {Y : Ω → G} : H[X-Y; μ] - H[X; μ] ≤ 2 * d[X ; μ # Y ; μ ] := by sorry

/-- $$  \bbH[X-Y] - \bbH[Y] \leq 2d[X;Y].$$ -/
lemma diff_ent_le_rdist'' {Y : Ω → G} : H[X-Y; μ] - H[X; μ] ≤ 2 * d[X ; μ # Y ; μ ] := by sorry

/--   $$ d[X;Y] \geq 0.$$  -/
lemma rdist_nonneg : 0 ≤ d[ X ; μ # Y ; μ' ] := by sorry

/-- The Ruzsa triangle inequality -/
lemma rdist_triangle (X : Ω → G) (Y : Ω' → G) (Z : Ω'' → G) :
    d[ X ; μ # Z ; μ'' ] ≤ d[ X ; μ # Y ; μ' ] + d[ Y ; μ' # Z ; μ'' ] := sorry

/-- definition of d[ X|Z ; Y| W ]-/
def cond_rdist [MeasurableSpace S] [MeasurableSpace T] (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T) (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac): ℝ := sorry

notation3:max "d[" X " | " Z "; " μ " # " Y " | " W "; " μ'"]" => cond_rdist X Z Y W μ μ'

/-- definition of d[ X ; Y| W ]-/
def cond_rdist' [MeasurableSpace T] (X : Ω → G) (Y : Ω' → G) (W : Ω' → T) (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac): ℝ := sorry

notation3:max "d[" X "; " μ " # " Y " | " W "; " μ' "]" => cond_rdist' X Y W μ μ'

/-- $$  d[X  | Z;Y | W] = H[X'-Y'|Z',W'] - H[X'|Z']/2 - H[Y'|W']/2$$ -/
lemma cond_rdist_of_indep [MeasurableSpace S] [MeasurableSpace T] {X : Ω → G} {Z : Ω → S} {Y : Ω → G} {W : Ω → T} (h : IndepFun (⟨X, Z⟩) (⟨ Y, W ⟩) μ) : d[ X | Z ; μ # Y | W ; μ] = H[X-Y | ⟨ Z, W ⟩; μ ] - H[X | Z; μ ]/2 - H[Y | W; μ ]/2 := by sorry

lemma cond_rdist'_of_indep  [MeasurableSpace T] {X : Ω → G} {Y : Ω → G} {W : Ω → T} (h : IndepFun X (⟨ Y, W ⟩) μ) : d[ X ; μ # Y | W ; μ] = H[X-Y | W; μ ] - H[X; μ ]/2 - H[Y | W; μ ]/2 := by sorry

lemma cond_rdist_of_copy : 0 = 1 := by sorry

lemma cond_rdist'_of_copy : 0 = 1 := by sorry


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


end Balog_Szemeredi_Gowers


/--   Suppose that $(X, Z)$ and $(Y, W)$ are random variables, where $X, Y$ take values in an abelian group. Then
$$   d[X  | Z;Y | W] \leq d[X; Y] + \tfrac{1}{2} I[X : Z] + \tfrac{1}{2} I[Y : W].$$
-/
lemma condDist_le : 0 = 1 := by sorry


/-- Let $X, Y, Z$ be random variables taking values in some abelian group, and with $Y, Z$ independent. Then we have
  $$ d[X; Y + Z] -d[X; Y]  \leq \tfrac{1}{2} (H[Y+Z] - H[Y]) $$
  $$ = \tfrac{1}{2} d[Y; Z] + \tfrac{1}{4} H[Z] - \tfrac{1}{4} H[Y]$$
  and
$$
  d[X;Y|Y+Z] - d[X;Y] \leq \tfrac{1}{2} \bigl(H[Y+Z] - H[Z]\bigr) $$
   = \tfrac{1}{2} d[Y;Z] + \tfrac{1}{4} H[Y] - \tfrac{1}{4} H[Z].
-/
lemma condDist_le' : 0 = 1 := by sorry


/--   Let $X, Y, Z, Z'$ be random variables taking values in some abelian group, and with $Y, Z, Z'$ independent. Then we have
$$ d[X;Y + Z | Y + Z + Z'] - d[X;Y] $$
$$ \leq \tfrac{1}{2} ( H[Y + Z + Z'] + H[Y + Z] - H[Y] - H[Z']).$$
-/
lemma condDist_le'' : 0 = 1 := by sorry
