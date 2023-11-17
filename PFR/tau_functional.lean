
import PFR.f2_vec
import PFR.ruzsa_distance

/-!
# The tau functional

Definition of the tau functional and basic facts

-/
open MeasureTheory ProbabilityTheory

variable (Ω₀₁ Ω₀₂ : Type*) [MeasurableSpace Ω₀₁] [MeasurableSpace Ω₀₂]
variable (G : Type*) [AddCommGroup G] [ElementaryAddGroup G 2] [Fintype G] [MeasurableSpace G]

structure ref_package :=
  μ₀₁ : Measure Ω₀₁
  μ₀₂ : Measure Ω₀₂
  h1 : IsProbabilityMeasure μ₀₁
  h2 : IsProbabilityMeasure μ₀₂
  X₀₁ : Ω₀₁ → G
  X₀₂ : Ω₀₂ → G
  hmeas1 : Measurable X₀₁
  hmeas2 : Measurable X₀₂


variable (p : ref_package Ω₀₁ Ω₀₂ G)
variable {Ω₀₁ Ω₀₂ G}

variable {Ω₁ Ω₁ Ω'₁ Ω'₂ : Type*} [MeasurableSpace Ω₁] (μ₁ : Measure Ω₁)
  [MeasurableSpace Ω₂] (μ₂ : Measure Ω₂) [MeasurableSpace Ω'₁] (μ'₁ : Measure Ω'₁)
  [MeasurableSpace Ω'₂] (μ'₂ : Measure Ω'₂)

variable (X₁ : Ω₁ → G) (X₂ : Ω₂ → G)

noncomputable def eta := (9:ℝ)⁻¹

/-- If $X_1,X_2$ are two $G$-valued random variables, then
$$  \tau[X_1; X_2] \coloneqq d[X_1; X_2] + \eta  d[X^0_1; X_1] + \eta d[X^0_2; X_2].$$
Here, $X^0_1$ and $X^0_2$ are two random variables fixed once and for all in most of the argument.
To lighten notation, We package `X^0_1` and `X^0_2` in a single object named `p`. --/
noncomputable def tau (X₁ : Ω₁ → G) (μ₁ : Measure Ω₁) (X₂ : Ω₂ → G) (μ₂ : Measure Ω₂) : ℝ :=
  d[X₁ ; μ₁ # X₂ ; μ₂] + eta * d[p.X₀₁ ; p.μ₀₁ # X₁ ; μ₁] + eta * d[p.X₀₂ ; p.μ₀₂ # X₂ ; μ₂]

notation3:max "τ[" X₁ " ; " μ₁ " # " X₂ " ; " μ₂ " | " p"]" => tau p X₁ μ₁ X₂ μ₂

/-- If $X'_1, X'_2$ are copies of $X_1,X_2$, then $\tau[X'_1;X'_2] = \tau[X_1;X_2]$. --/
lemma ProbabilityTheory.IdentDistrib.tau_eq
   (h₁ : IdentDistrib X₁ X'₁ μ₁ μ'₁) (h₂ : IdentDistrib X₂ X'₂ μ₂ μ'₂) :
    τ[X₁ ; μ₁ # X₂ ; μ₂ | p] = τ[X'₁ ; μ'₁ # X'₂ ; μ'₂ | p] := by
  simp only [tau]
  rw [(IdentDistrib.refl p.hmeas1.aemeasurable).rdist_eq h₁,
      (IdentDistrib.refl p.hmeas2.aemeasurable).rdist_eq h₂,
      h₁.rdist_eq h₂]

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
