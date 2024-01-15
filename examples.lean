import PFR.ApproxHomPFR
import PFR.ImprovedPFR
import PFR.WeakPFR

section PFR

open Pointwise

variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [Fintype G]

variable {G' : Type*} [AddCommGroup G'] [Module (ZMod 2) G'] [Fintype G']

/-- A self-contained version of the PFR conjecture using only Mathlib definitions. -/
example {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 12 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  convert PFR_conjecture h₀A hA
  norm_cast

#print axioms PFR_conjecture

/-- The improved version -/
example {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 11 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  convert PFR_conjecture_improv h₀A hA
  norm_cast

#print axioms PFR_conjecture_improv

/-- The homomorphism version of PFR. -/
example (f : G → G') (S : Set G') (hS : ∀ x y : G, f (x + y) - f x - f y ∈ S) :
    ∃ (φ : G →+ G') (T : Set G'), Nat.card T ≤ (Nat.card S)^12 ∧ ∀ x, f x - φ x ∈ T := homomorphism_pfr f S hS

-- Todo: replace the constants C₁, C₂, C₃, C₄ below with actual values

/-- The approximate homomorphism version of PFR -/
example (f : G → G') (K : ℝ) (hK: K > 0) (hf: Nat.card { x : G × G| f (x.1+x.2) = (f x.1) + (f x.2) } ≥ (Nat.card G)^2/ K) : ∃ (φ : G →+ G') (c : G'), Nat.card { x : G | f x = φ x + c } ≥ (Nat.card G) / (4 * C₁^21 * C₃^20 * K^(46 * C₄ + 44 * C₂)) := by
  convert approx_hom_pfr f K hK hf

open Classical TensorProduct Real

/-- The dimension of a subset A of a Z-module G is the minimal rank of a coset of G that covers A. -/
example {G : Type*} [AddCommGroup G] (A : Set G) :  ∃ (S : Submodule ℤ G) (v : G), FiniteDimensional.finrank ℤ S = dimension A  ∧ ∀ a ∈ A, a - v ∈ S := Nat.find_spec (exists_coset_cover A)

example {G : Type*} [AddCommGroup G] (A : Set G) (d:ℕ) (h: d < dimension A): ¬ ∃ (S : Submodule ℤ G) (v : G), FiniteDimensional.finrank ℤ S = d ∧ ∀ a ∈ A, a - v ∈ S := Nat.find_min (exists_coset_cover A) h


#print axioms weak_PFR_int

variable  {G : Type u} [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G] [Countable G]  [MeasurableSpace G] [MeasurableSingletonClass G]

/-- Weak PFR over the integers -/
example (A : Set G) [Finite A]  [Nonempty A] (K : ℝ) (hK: 0 < K) (hA: Nat.card (A-A) ≤ K * Nat.card A) : ∃ A' : Set G, A' ⊆ A ∧ (Nat.card A') ≥ K^(-17 : ℝ) * (Nat.card A) ∧ (dimension A') ≤ (40/log 2) * log K := weak_PFR_int hK hA

end PFR



section RealMeasure
-- some examples to showcase real-valued measures in a self-contained fashion.

open MeasureTheory ProbabilityTheory BigOperators

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- The probability measure ℙ, but taking values in the reals. Can be more convenient than ENNReal-valued measures if one wishes to use operations such as subtraction. -/
local notation3 "ℙᵣ" => (ℙ : Measure Ω).real

example (E : Set Ω) : ℙᵣ E = (ℙ E).toReal := by rfl

example : ℙᵣ Set.univ = 1 := by simp

example {A : Type*} [Fintype A] (E : A → Set Ω) : ℙᵣ (⋃ a, E a) ≤ ∑ a, ℙᵣ (E a) :=
  measureReal_iUnion_fintype_le E

example {A : Type*} [Fintype A] (E : A → Set Ω)   (hn : Pairwise (Disjoint on E)) (h : ∀ i, MeasurableSet (E i))
: ℙᵣ (⋃ a, E a) = ∑ a, ℙᵣ (E a) :=
  measureReal_iUnion_fintype hn h

/-- A simple example of applying real-valued subtraction. -/
example (E F : Set Ω) (h : NullMeasurableSet F ℙ)
 : ℙᵣ (E ∩ F) = ℙᵣ E - ℙᵣ (E \ F) := by
  rw [← measureReal_inter_add_diff₀ E h]
  ring

example (E : Set Ω) : 0 ≤ ℙᵣ E ∧ ℙᵣ E ≤ 1 := by
  constructor
  . simp
  have : E ⊆ Set.univ := by simp
  convert measureReal_mono (μ := ℙ) this
  simp


end RealMeasure


section Entropy
-- some examples to showcase Shannon entropy in a self-contained fashion.  For simplicity we only illustrate the notation for probability spaces with a canonical probability measure, but one can also decouple the measure from the space if desired.

open MeasureTheory ProbabilityTheory BigOperators

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {S : Type*} [Fintype S] [Nonempty S][MeasurableSpace S] [MeasurableSingletonClass S]

variable {T : Type*} [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]

variable {U : Type*} [Fintype U] [Nonempty U][MeasurableSpace U] [MeasurableSingletonClass U]

variable (X : Ω → S) (hX : Measurable X) (Y : Ω → T) (hY : Measurable Y) (Z : Ω → U)
  (hZ : Measurable Z)

/-- $H[X]$ is the Shannon entropy of $X$. -/
example :
    H[X] =
      -∑ x, ((ℙ : Measure Ω).map X {x}).toReal * Real.log ((ℙ : Measure Ω).map X {x}).toReal := by
  rw [entropy_eq_sum hX ℙ, ← Finset.sum_neg_distrib, tsum_eq_sum]
  . congr with x
    unfold Real.negMulLog
    ring
  intro x hx
  simp at hx

/-- $\langle X,Y \rangle$ is the random variable formed by pairing $X$ and $Y$. -/

example (ω : Ω) : (⟨X, Y⟩) ω = (X ω, Y ω) := rfl

/-- $H[X|Y]$ is the conditional entropy of $X$ relative to $Y$. -/
example : H[X|Y] = H[⟨X,Y⟩] - H[Y] := chain_rule'' ℙ hX hY

/-- $I[X:Y]$ is the mutual information between $X$ and $Y$. -/
example : I[X:Y] = H[X] + H[Y] - H[⟨X,Y⟩] := rfl

/-- $I[X:Y|Z]$ is the conditional mutual information between $X$ and $Y$ relative to $Z$. -/
example : I[X:Y|Z] = H[X|Z] + H[Y|Z] - H[⟨X,Y⟩|Z] := condMutualInfo_eq hX hY hZ ℙ

/-- Submodularity: conditional information is nonnegative. -/
example : 0 ≤ I[X : Y | Z] := condMutualInfo_nonneg hX hY Z ℙ

/-- Relation between conditional mutual information and conditional independence. -/
example : I[X : Y | Z] = 0 ↔ CondIndepFun X Y Z := condMutualInfo_eq_zero hX hY hZ


end Entropy


section RuzsaDistance
-- some examples to showcase Ruzsa distance in a self-contained fashion

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {G : Type*} [hG: MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Fintype G]

variable (X : Ω → G) (hX : Measurable X) (Y : Ω → G) (hY : Measurable Y) (Z : Ω → G)
  (hZ : Measurable Z) (X' Y' : Ω → G)

/-- `d[X # Y]` is the Ruzsa distance when `X`, `Y` are independent. -/
example (h : IndepFun X Y) : d[X # Y] = H[X-Y] - H[X]/2 - H[Y]/2 := h.rdist_eq hX hY

/-- `d[X # Y]` depends only on the distribution of `X` and `Y`.-/
example (h1 : IdentDistrib X X') (h2 : IdentDistrib Y Y') : d[X # Y] = d[X' # Y'] := h1.rdist_eq h2

/-- The Ruzsa triangle inequality. -/
example : d[X # Z] ≤ d[X # Y] + d[Y # Z] := rdist_triangle hX hY hZ

/-- The Kaimanovich-Vershik-Madiman inequality -/
example (h : iIndepFun (fun _ ↦ hG) ![X, Y, Z]) : H[X + Y + Z] - H[X + Y] ≤ H[Y + Z] - H[Y] :=
  kaimanovich_vershik h hX hY hZ

/-- The entropic Balog--Szemeredi--Gowers inequality -/
example (h : Z = X + Y) :
    ((ℙ : Measure Ω).map Z)[fun z ↦ d[X ; ℙ[|Z ← z] # Y ; ℙ[|Z ← z]]]
      ≤ 3 * I[X : Y] + 2 * H[Z] - H[X] - H[Y] := by subst h; exact ent_bsg hX hY

end RuzsaDistance

section Finiteness
-- some examples to showcase the Finiteness tactic

open ENNReal

example : (1:ℝ≥0∞) < ∞ := by finiteness

example : (3:ℝ≥0∞) ≠ ∞ := by finiteness

example (a : ℝ) (b : ℕ) : ENNReal.ofReal a + b < ∞ := by finiteness

example {a : ℝ≥0∞} (ha : a ≠ ∞) : a + 3 < ∞ := by finiteness
example {a : ℝ≥0∞} (ha : a < ∞) : a + 3 < ∞ := by finiteness

example (a : ℝ) : (ENNReal.ofReal (1 + a ^ 2))⁻¹ < ∞ := by finiteness

example (f : α → ℕ) : ∀ i, (f i : ℝ≥0∞) ≠ ∞ := by finiteness

open MeasureTheory

example {Ω Ω': Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] [MeasurableSpace Ω']
    (μ' : Measure Ω') [IsFiniteMeasure μ'] (E : Set (Ω × Ω')) : (μ.prod μ') E < ∞ := by finiteness


end Finiteness
