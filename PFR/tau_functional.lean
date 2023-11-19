
import PFR.f2_vec
import PFR.ruzsa_distance

/-!
# The tau functional

Definition of the tau functional and basic facts
-/

open MeasureTheory ProbabilityTheory
universe u


/-- For mathlib -/
lemma identDistrib_id {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {X : α → β} (hX : AEMeasurable X μ) :
    IdentDistrib X id μ (μ.map X) where
  aemeasurable_fst := hX
  aemeasurable_snd := aemeasurable_id
  map_eq := by simp


variable (Ω₀₁ Ω₀₂ : Type*) [MeasurableSpace Ω₀₁] [MeasurableSpace Ω₀₂]
variable (G : Type u) [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G]

/-- A structure that packages all the fixed information in the main argument. In this way, when
defining the τ functional, we will only only need to refer to the package once in the notation
instead of stating the reference spaces, the reference measures and the reference random
variables. -/
structure refPackage :=
  μ₀₁ : Measure Ω₀₁
  μ₀₂ : Measure Ω₀₂
  h1 : IsProbabilityMeasure μ₀₁
  h2 : IsProbabilityMeasure μ₀₂
  X₀₁ : Ω₀₁ → G
  X₀₂ : Ω₀₂ → G
  hmeas1 : Measurable X₀₁
  hmeas2 : Measurable X₀₂


variable (p : refPackage Ω₀₁ Ω₀₂ G)
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
@[pp_dot] noncomputable def tau
    (X₁ : Ω₁ → G) (μ₁ : Measure Ω₁) (X₂ : Ω₂ → G) (μ₂ : Measure Ω₂) : ℝ :=
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

instance : MeasurableSpace (G × G) := by infer_instance


/- We will now construct random variables minimizing the tau functional. Their existence follows
from the continuity of the functional on the (compact) space of measures on the group. To rephrase
it in random variables terms with a convenient access to them, we introduce a space `p.Ω` with a
probability measure `p.μ` and two random variables `p.X₁, p.X₂ : p.Ω → G` that minimize the
functional, i.e., such that their value is smaller than the one over any pair of random variables.
The space `p.Ω` is constructed as `G × G` and the variables `p.X₁` and `p.X₂` as the first and
second projections, but this should be seen as an irrelevant implementation detail. -/

@[pp_dot] def refPackage.Ω (p : refPackage Ω₀₁ Ω₀₂ G) := G × G

instance : MeasurableSpace p.Ω := inferInstanceAs (MeasurableSpace (G × G))

@[pp_dot] def refPackage.X₁ (p : refPackage Ω₀₁ Ω₀₂ G) : p.Ω → G := Prod.fst
@[pp_dot] def refPackage.X₂ (p : refPackage Ω₀₁ Ω₀₂ G) : p.Ω → G := Prod.snd

lemma tau_min_exists_measure : ∃ (μ : Measure G × Measure G),
    IsProbabilityMeasure μ.1 ∧ IsProbabilityMeasure μ.2 ∧
    ∀ (ν₁ : Measure G) (ν₂ : Measure G), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      τ[id ; μ.1 # id ; μ.2 | p] ≤ τ[id ; ν₁ # id ; ν₂ | p] := sorry

@[pp_dot] noncomputable def refPackage.μ (p : refPackage Ω₀₁ Ω₀₂ G) : Measure p.Ω := by
  let μ := (tau_min_exists_measure p).choose
  exact μ.1.prod μ.2

instance : IsProbabilityMeasure p.μ := by
  have := (tau_min_exists_measure p).choose_spec.1
  have := (tau_min_exists_measure p).choose_spec.2.1
  exact MeasureTheory.Measure.prod.instIsProbabilityMeasure _ _

lemma is_tau_min
    {X'₁ : Ω'₁ → G} {X'₂ : Ω'₂ → G} (h1 : Measurable X'₁) (h2 : Measurable X'₂)
    [IsProbabilityMeasure μ'₁] [IsProbabilityMeasure μ'₂] :
    τ[p.X₁ ; p.μ # p.X₂ ; p.μ | p] ≤ τ[X'₁ ; μ'₁ # X'₂ ; μ'₂ | p] := by
  let ν₁ := μ'₁.map X'₁
  let ν₂ := μ'₂.map X'₂
  let μ := (tau_min_exists_measure p).choose
  have A : τ[p.X₁ ; p.μ # p.X₂ ; p.μ | p] = τ[id ; μ.1 # id ; μ.2 | p] := sorry
  have B : τ[X'₁ ; μ'₁ # X'₂ ; μ'₂ | p] = τ[id ; ν₁ # id ; ν₂ | p] := sorry
  convert (tau_min_exists_measure p).choose_spec.2.2
    ν₁ ν₂ (isProbabilityMeasure_map h1.aemeasurable) (isProbabilityMeasure_map h2.aemeasurable)

/-- Let `X₁` and `X₂` be the tau-minimizers associated to `p`, with $d[X_1,X_2]=k$, then
$$ d[X'_1;X'_2] \geq k - \eta (d[X^0_1;X'_1] - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2] - d[X^0_2;X_2] )$$
for any $G$-valued random variables $X'_1,X'_2$.
-/
lemma distance_ge_of_min
    {X'₁ : Ω'₁ → G} {X'₂ : Ω'₂ → G} (h1 : Measurable X'₁) (h2 : Measurable X'₂)
    [IsProbabilityMeasure μ'₁] [IsProbabilityMeasure μ'₂] :
    d[p.X₁ ; p.μ # p.X₂ ; p.μ] - η * (d[p.X₀₁ ; p.μ₀₁ # X'₁ ; μ'₁] - d[p.X₀₁ ; p.μ₀₁ # p.X₁ ; p.μ])
      - η * (d[p.X₀₂ ; p.μ₀₂ # X'₂ ; μ'₂] - d[p.X₀₂ ; p.μ₀₂ # p.X₂ ; p.μ])
    ≤ d[X'₁ ; μ'₁ # X'₂ ; μ'₂] := by
  have Z := is_tau_min p μ'₁ μ'₂ h1 h2
  simp [tau] at Z
  linarith

/--   For any $G$-valued random variables $X'_1,X'_2$ and random variables $Z,W$, one has
$$ d[X'_1|Z;X'_2|W] \geq k - \eta (d[X^0_1;X'_1|Z]
  - d[X^0_1;X_1] ) - \eta (d[X^0_2;X'_2|W] - d[X^0_2;X_2] ).$$
-/
lemma condDistance_ge_of_min [MeasurableSpace S] [MeasurableSpace T]
    {X'₁ : Ω'₁ → G} {X'₂ : Ω'₂ → G} (h1 : Measurable X'₁) (h2 : Measurable X'₂)
    [IsProbabilityMeasure μ'₁] [IsProbabilityMeasure μ'₂] (Z : Ω'₁ → S) (W : Ω'₂ → T):
    d[p.X₁ ; p.μ # p.X₂ ; p.μ] - η * (d[p.X₀₁ ; p.μ₀₁ # X'₁ | Z ; μ'₁] - d[p.X₀₁ ; p.μ₀₁ # p.X₁ ; p.μ])
      - η * (d[p.X₀₂ ; p.μ₀₂ # X'₂ | W; μ'₂] - d[p.X₀₂ ; p.μ₀₂ # p.X₂ ; p.μ])
    ≤ d[X'₁ | Z ; μ'₁ # X'₂ | W ; μ'₂] := sorry
