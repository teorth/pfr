import Mathlib.Probability.Notation
import PFR.Mathlib.Probability.Independence.Basic
import PFR.ForMathlib.Pair

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} [MeasureSpace Ω]
  {G : Type*} [hG : MeasurableSpace G]

variable {Z₁ Z₂ Z₃ : Ω → G} (h_indep : iIndepFun (fun _i => hG) ![Z₁, Z₂, Z₃])

include h_indep

lemma reindex_three_abc :
    iIndepFun (fun _ => hG) ![Z₁, Z₂, Z₃] := h_indep

lemma reindex_three_acb :
    iIndepFun (fun _ => hG) ![Z₁, Z₃, Z₂] := by
  let σ : Fin 3 ≃ Fin 3 :=
  { toFun := ![0, 2, 1],
    invFun := ![0, 2, 1],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_three_bac :
    iIndepFun (fun _ => hG) ![Z₂, Z₁, Z₃] := by
  let σ : Fin 3 ≃ Fin 3 :=
  { toFun := ![1, 0, 2],
    invFun := ![1, 0, 2],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_three_bca :
    iIndepFun (fun _ => hG) ![Z₂, Z₃, Z₁] := by
  let σ : Fin 3 ≃ Fin 3 :=
  { toFun := ![1, 2, 0],
    invFun := ![2, 0, 1],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_three_cab :
    iIndepFun (fun _ => hG) ![Z₃, Z₁, Z₂] := by
  let σ : Fin 3 ≃ Fin 3 :=
  { toFun := ![2, 0, 1],
    invFun := ![1, 2, 0],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_three_cba :
    iIndepFun (fun _ => hG) ![Z₃, Z₂, Z₁] := by
  let σ : Fin 3 ≃ Fin 3 :=
  { toFun := ![2, 1, 0],
    invFun := ![2, 1, 0],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

private abbrev κ : Fin 2 → Type
  | 0 => Fin 1
  | 1 => Fin 2

private def κ_equiv : (Σ i, κ i) ≃ Fin 3 where
  toFun := fun x ↦ match x with
    | Sigma.mk 0 _ => 0
    | Sigma.mk 1 ⟨0, _⟩ => 1
    | Sigma.mk 1 ⟨1, _⟩ => 2
  invFun := ![Sigma.mk 0 ⟨0, zero_lt_one⟩,
    Sigma.mk 1 ⟨0, zero_lt_two⟩, Sigma.mk 1 ⟨1, one_lt_two⟩]
  left_inv := by rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def fintype_kappa : ∀ (i : Fin 2), Fintype (κ i)
  | 0 | 1 => inferInstanceAs (Fintype (Fin _))

variable (G) in
private abbrev self_or_prod : Fin 2 → Type _
  | 0 => G
  | 1 => G × G

attribute [local instance] fintype_kappa in
lemma pair_last_of_three
    (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) :
    IndepFun Z₁ (⟨Z₂, Z₃⟩) := by
  have T := iIndepFun.pi' (m := fun _ _ ↦ hG) ?_ (h_indep.reindex_symm κ_equiv); swap
  · rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> assumption
  -- apply to this pair of independent variables the function mapping the latter pair (as
  -- a function on `Fin 2`) to the same pair, but in the product space sense.
  -- It retains independence, proving the conclusion.
  let phi_third : ∀ (i : Fin 2), (κ i → G) → (self_or_prod G i)
    | 0 => (fun f ↦ f ⟨0, zero_lt_one⟩)
    | 1 => (fun f ↦ (f ⟨0, zero_lt_two⟩, f ⟨1, one_lt_two⟩))
  let M i : MeasurableSpace (self_or_prod G i) := by match i with | 0 | 1 => infer_instance
  have := T.comp phi_third
  refine (this ?_).indepFun (i := 0) (j := 1) zero_ne_one
  intro i
  match i with
  | 0 | 1 => fun_prop
