
import PFR.f2_vec
import PFR.ruzsa_distance

/-!
# The tau functional

Definition of the tau functional and basic facts
-/

open MeasureTheory ProbabilityTheory

/-- For mathlib -/
lemma identDistrib_id {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {X : α → β} (hX : AEMeasurable X μ) :
    IdentDistrib X id μ (μ.map X) where
  aemeasurable_fst := hX
  aemeasurable_snd := aemeasurable_id
  map_eq := by simp


variable (Ω₀₁ Ω₀₂ : Type*) [MeasurableSpace Ω₀₁] [MeasurableSpace Ω₀₂]
variable (G : Type*) [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G]

/-- A structure that packages all the fixed information in the main argument. In this way, when
defining the τ functional, we will only only need to refer to the package once in the notation
instead of stating the reference spaces, the reference measures and the reference random
variables. -/
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

noncomputable def η := (9:ℝ)⁻¹

/-- If $X_1,X_2$ are two $G$-valued random variables, then
$$  \tau[X_1; X_2] \coloneqq d[X_1; X_2] + \eta  d[X^0_1; X_1] + \eta d[X^0_2; X_2].$$
Here, $X^0_1$ and $X^0_2$ are two random variables fixed once and for all in most of the argument.
To lighten notation, We package `X^0_1` and `X^0_2` in a single object named `p`.

We denote it as `τ[X₁ ; μ₁ # X₂ ; μ₂ | p]` where `p` is a fixed package containing the information
of the reference random variables.
--/
noncomputable def tau (X₁ : Ω₁ → G) (μ₁ : Measure Ω₁) (X₂ : Ω₂ → G) (μ₂ : Measure Ω₂) : ℝ :=
  d[X₁ ; μ₁ # X₂ ; μ₂] + η * d[p.X₀₁ ; p.μ₀₁ # X₁ ; μ₁] + η * d[p.X₀₂ ; p.μ₀₂ # X₂ ; μ₂]

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
for all $G$-valued random variables $X'_1, X'_2$. To avoid conditioning over all spaces in the
definition, we formulate the definition in terms of measures in the group itself (i.e., `X₁` will
be the identity and `μ₁` a measure on `G`, and likewise for `μ₂`, and we compare these to other
measures on the group), but then it will imply the same property generally, see
`distance_ge_of_min`. --/
structure tau_minimizes (μ₁ : Measure G) (μ₂ : Measure G) : Prop :=
  h₁ : IsProbabilityMeasure μ₁
  h₂ : IsProbabilityMeasure μ₂
  hmin : ∀ (ν₁ : Measure G) (ν₂ : Measure G), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      τ[id ; μ₁ # id ; μ₂ | p] ≤ τ[id ; ν₁ # id ; ν₂ | p]

/--  There exist $G$-valued random variables $X_1, X_2$ such that tau_minimizes holds.
-/
lemma tau_min_exists : ∃ (μ₁ μ₂ : Measure G), tau_minimizes p μ₁ μ₂ := sorry

variable {p}

/-- If $X_1,X_2$ are tau-minimizers with $d[X_1,X_2]=k$, then
$$ d[X'_1;X'_2] \geq k - \eta (d[X^0_1;X'_1] - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2] - d[X^0_2;X_2] )$$
for any $G$-valued random variables $X'_1,X'_2$.
-/
lemma distance_ge_of_min {μ₁ μ₂ : Measure G} (h : tau_minimizes p μ₁ μ₂)
    {X'₁ : Ω'₁ → G} {X'₂ : Ω'₂ → G} (h1 : Measurable X'₁) (h2 : Measurable X'₂)
    [IsProbabilityMeasure μ'₁] [IsProbabilityMeasure μ'₂] :
    d[id ; μ₁ # id ; μ₂] - η * (d[p.X₀₁ ; p.μ₀₁ # X'₁ ; μ'₁] - d[p.X₀₁ ; p.μ₀₁ # id ; μ₁])
      - η * (d[p.X₀₂ ; p.μ₀₂ # X'₂ ; μ'₂] - d[p.X₀₂ ; p.μ₀₂ # id ; μ₂])
    ≤ d[X'₁ ; μ'₁ # X'₂ ; μ'₂] := by
  let ν₁ := μ'₁.map X'₁
  let ν₂ := μ'₂.map X'₂
  have Z := h.hmin ν₁ ν₂ (isProbabilityMeasure_map h1.aemeasurable)
    (isProbabilityMeasure_map h2.aemeasurable)
  simp [tau] at Z
  have A : d[id ; Measure.map X'₁ μ'₁ # id ; Measure.map X'₂ μ'₂] = d[X'₁ ; μ'₁ # X'₂ ; μ'₂] :=
    (identDistrib_id h1.aemeasurable).symm.rdist_eq  (identDistrib_id h2.aemeasurable).symm
  have B : d[p.X₀₁ ; p.μ₀₁ # id ; Measure.map X'₁ μ'₁] = d[p.X₀₁ ; p.μ₀₁ # X'₁ ; μ'₁] :=
    (IdentDistrib.refl p.hmeas1.aemeasurable).rdist_eq (identDistrib_id h1.aemeasurable).symm
  have C : d[p.X₀₂ ; p.μ₀₂ # id ; Measure.map X'₂ μ'₂] = d[p.X₀₂ ; p.μ₀₂ # X'₂ ; μ'₂] :=
    (IdentDistrib.refl p.hmeas2.aemeasurable).rdist_eq (identDistrib_id h2.aemeasurable).symm
  rw [A, B, C, ← sub_nonneg] at Z
  rw [← sub_nonneg]
  convert Z using 1
  ring

/--   For any $G$-valued random variables $X'_1,X'_2$ and random variables $Z,W$, one has
$$ d[X'_1|Z;X'_2|W] \geq k - \eta (d[X^0_1;X'_1|Z] - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2|W] - d[X^0_2;X_2] ).$$
-/
lemma condDistance_ge_of_min [MeasurableSpace S] [MeasurableSpace T] {μ₁ μ₂ : Measure G} (h : tau_minimizes p μ₁ μ₂)
    {X'₁ : Ω'₁ → G} {X'₂ : Ω'₂ → G} (h1 : Measurable X'₁) (h2 : Measurable X'₂)
    [IsProbabilityMeasure μ'₁] [IsProbabilityMeasure μ'₂] (Z : Ω'₁ → S) (W : Ω'₂ → T):
    d[id ; μ₁ # id ; μ₂] - η * (d[p.X₀₁ ; p.μ₀₁ # X'₁ | Z ; μ'₁] - d[p.X₀₁ ; p.μ₀₁ # id ; μ₁])
      - η * (d[p.X₀₂ ; p.μ₀₂ # X'₂ | W; μ'₂] - d[p.X₀₂ ; p.μ₀₂ # id ; μ₂])
    ≤ d[X'₁ | Z ; μ'₁ # X'₂ | W ; μ'₂] := sorry
