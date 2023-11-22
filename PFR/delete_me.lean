import Mathlib.Probability.Notation
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import PFR.Entropy.Group
import PFR.entropy_basic
import PFR.ForMathlib.CompactProb
import PFR.ruzsa_distance

universe u_1

open MeasureTheory ProbabilityTheory

variable  {Ω Ω' Ω'' Ω''' G T : Type u_1} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [mΩ'' : MeasurableSpace Ω''] [hG : MeasurableSpace G] {μ : Measure Ω} {μ' : Measure Ω'}
  {μ'' : Measure Ω''}  [hG: MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Fintype G]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
/-- The Ruzsa triangle inequality -/
lemma rdist_triangle'' (X : Ω → G) (Y : Ω' → G) (Z : Ω'' → G)
   (hX: Measurable X) (hY: Measurable Y)
  (hZ : Measurable Z)
  [IsFiniteMeasure μ] :
    d[ X ; μ # Z ; μ'' ] ≤ d[ X ; μ # Y ; μ' ] + d[ Y ; μ' # Z ; μ'' ] := by
  let S  := ![G,G,G]
  let ω := ![Ω, Ω', Ω'']
  haveI mS : ∀ i : Fin 3, MeasurableSpace (S i) := fun i => by
    have : S i = G
    · fin_cases i ; all_goals { simp }
    rwa [this]
  haveI mΩ : ∀ i : Fin 3, (MeasurableSpace (ω i)) :=
    Fin.cons mΩ (Fin.cons mΩ' (Fin.cons mΩ'' (show (i : Fin 0) → MeasurableSpace (ω i.succ.succ.succ) from sorry)))
  let Vars : ∀ i : Fin 3, ω i → S i :=
    Fin.cons X (Fin.cons Y (Fin.cons Z (show (i : Fin 0) → ω i.succ.succ.succ → S i.succ.succ.succ from sorry)))
  have hVars : ∀ i : Fin 3, Measurable (Vars i) :=
    sorry --Fin.cons hX (Fin.cons hY (Fin.cons hZ (show ∀ (i : Fin 0), Measurable (Vars i.succ.succ.succ) from sorry)))
  have m : ∀ i : Fin 3, Measure (ω i) := sorry
  obtain ⟨A, mA, μA, X, hμA, _, hX⟩ := independent_copies' Vars hVars m

  suffices : ∀ (X Y Z : A → G) (hv : IsFiniteMeasure μA) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h₁ : IndepFun X Y μA) (h₂ : IndepFun Y Z μA) (h₃ : IndepFun X Z μA),
    d[ X ; μA # Z ; μA ] ≤ d[ X ; μA # Y ; μA ] + d[ Y ; μA # Z ; μA ]
  {

    --have lem := this (X 0) (X 1) (X 2) sorry (by exact (hX 0).left)
    have temp : @Measurable A G mA hG (X 0)
    exact (hX 0).left
    rw [←ProbabilityTheory.IdentDistrib.rdist_eq HX HY,
      ←ProbabilityTheory.IdentDistrib.rdist_eq HY HZ, ←ProbabilityTheory.IdentDistrib.rdist_eq HX HZ]
  }
  intros X Y Z hμA hX hY hZ h₁ h₂ h₃
  calc d[ X ; μA # Z ; μA ] = H[X - Z; μA] - (H[X; μA] / 2 + H[Z; μA] / 2) := by
        rw [ProbabilityTheory.IndepFun.rdist_eq h₃ hX hZ] ; ring
    _  ≤ (H[X - Y ; μA] + H[Y - Z ; μA] - H[Y ; μA]) - (H[X; μA] / 2 + H[Z; μA] / 2) :=
          sub_le_sub_right (ent_of_diff_le X Y Z (show IndepFun (⟨ X, Z ⟩) Y μA from sorry)) _
    _ = (H[X - Y ; μA] - H[X; μA] / 2 - H[Y ; μA] / 2) + (H[Y - Z ; μA] - H[Y ; μA] / 2 -  H[Z; μA] / 2) := by ring
    _ = d[ X ; μA # Y ; μA ] + d[ Y ; μA # Z ; μA ] := by
        rw [ProbabilityTheory.IndepFun.rdist_eq h₁ hX hY, ProbabilityTheory.IndepFun.rdist_eq h₂ hY hZ]
