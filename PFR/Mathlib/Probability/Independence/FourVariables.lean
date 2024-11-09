import Mathlib.Probability.Notation
import PFR.Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} [MeasureSpace Ω]
  {G : Type*} [hG : MeasurableSpace G]

variable {Z₁ Z₂ Z₃ Z₄ : Ω → G} (h_indep : iIndepFun (fun _i => hG) ![Z₁, Z₂, Z₃, Z₄])

include h_indep

lemma reindex_four_abcd :
    iIndepFun (fun _ => hG) ![Z₁, Z₂, Z₃, Z₄] := h_indep

lemma reindex_four_abdc :
    iIndepFun (fun _ => hG) ![Z₁, Z₂, Z₄, Z₃] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![0, 1, 3, 2],
    invFun := ![0, 1, 3, 2],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_acbd :
    iIndepFun (fun _ => hG) ![Z₁, Z₃, Z₂, Z₄] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![0, 2, 1, 3],
    invFun := ![0, 2, 1, 3],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_acdb :
    iIndepFun (fun _ => hG) ![Z₁, Z₃, Z₄, Z₂] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![0, 2, 3, 1],
    invFun := ![0, 3, 1, 2],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_adbc :
    iIndepFun (fun _ => hG) ![Z₁, Z₄, Z₂, Z₃] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![0, 3, 1, 2],
    invFun := ![0, 2, 3, 1],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_adcb :
    iIndepFun (fun _ => hG) ![Z₁, Z₄, Z₃, Z₂] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![0, 3, 2, 1],
    invFun := ![0, 3, 2, 1],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_bacd :
    iIndepFun (fun _ => hG) ![Z₂, Z₁, Z₃, Z₄] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 0, 2, 3],
    invFun := ![1, 0, 2, 3],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_badc :
    iIndepFun (fun _ => hG) ![Z₂, Z₁, Z₄, Z₃] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 0, 3, 2],
    invFun := ![1, 0, 3, 2],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_bcad :
    iIndepFun (fun _ => hG) ![Z₂, Z₃, Z₁, Z₄] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 2, 0, 3],
    invFun := ![2, 0, 1, 3],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_bcda :
    iIndepFun (fun _ => hG) ![Z₂, Z₃, Z₄, Z₁] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 2, 3, 0],
    invFun := ![3, 0, 1, 2],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_bdac :
    iIndepFun (fun _ => hG) ![Z₂, Z₄, Z₁, Z₃] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 3, 0, 2],
    invFun := ![2, 0, 3, 1],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_bdca :
    iIndepFun (fun _ => hG) ![Z₂, Z₄, Z₃, Z₁] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![1, 3, 2, 0],
    invFun := ![3, 0, 2, 1],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_cadb :
    iIndepFun (fun _ => hG) ![Z₃, Z₁, Z₄, Z₂] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![2, 0, 3, 1],
    invFun := ![1, 3, 0, 2],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_cbad :
    iIndepFun (fun _ => hG) ![Z₃, Z₂, Z₁, Z₄] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![2, 1, 0, 3],
    invFun := ![2, 1, 0, 3],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_dabc :
    iIndepFun (fun _ => hG) ![Z₄, Z₁, Z₂, Z₃] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![3, 0, 1, 2],
    invFun := ![1, 2, 3, 0],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_dacb :
    iIndepFun (fun _ => hG) ![Z₄, Z₁, Z₃, Z₂] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![3, 0, 2, 1],
    invFun := ![1, 3, 2, 0],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_dbac :
    iIndepFun (fun _ => hG) ![Z₄, Z₂, Z₁, Z₃] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![3, 1, 0, 2],
    invFun := ![2, 1, 3, 0],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

lemma reindex_four_dbca :
    iIndepFun (fun _ => hG) ![Z₄, Z₂, Z₃, Z₁] := by
  let σ : Fin 4 ≃ Fin 4 :=
  { toFun := ![3, 1, 2, 0],
    invFun := ![3, 1, 2, 0],
    left_inv := by intro i; fin_cases i <;> rfl,
    right_inv := by intro i; fin_cases i <;> rfl }
  refine iIndepFun.reindex σ.symm ?_
  convert h_indep using 1
  ext i
  fin_cases i <;> rfl

private abbrev κ : Fin 3 → Type
  | 0 | 1 => Fin 1
  | 2   => Fin 2

private def κ_equiv : (Σ i, κ i) ≃ Fin 4 where
  toFun := fun x ↦ match x with
    | Sigma.mk 0 _ => 0
    | Sigma.mk 1 _ => 1
    | Sigma.mk 2 ⟨0, _⟩ => 2
    | Sigma.mk 2 ⟨1, _⟩ => 3
  invFun := ![Sigma.mk 0 ⟨0, zero_lt_one⟩, Sigma.mk 1 ⟨0, zero_lt_one⟩,
    Sigma.mk 2 ⟨0, zero_lt_two⟩, Sigma.mk 2 ⟨1, one_lt_two⟩]
  left_inv := by rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def fintype_kappa : ∀ (i : Fin 3), Fintype (κ i)
  | 0 | 1 | 2 => inferInstanceAs (Fintype (Fin _))

attribute [local instance] fintype_kappa in
/-- If `(Z₁, Z₂, Z₃, Z₄)` are independent, so are `(Z₁, Z₂, φ Z₃ Z₄)` for any measurable `φ`. -/
lemma apply_two_last
    (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) (hZ₄ : Measurable Z₄)
    {phi : G → G → G} (hphi : Measurable phi.uncurry) :
    iIndepFun (fun _ ↦ hG) ![Z₁, Z₂, (fun ω ↦ phi (Z₃ ω) (Z₄ ω))] := by
  -- deduce from the assumption the independence of `Z₁`, `Z₂` and `(Z₃, Z₄)`.
  have T := iIndepFun.pi' (m := fun _ _ ↦ hG) ?_ (h_indep.reindex_symm κ_equiv); swap
  · rintro ⟨i, j⟩; fin_cases i <;> fin_cases j <;> assumption
  -- apply to this triplet of independent variables the function `phi` applied to `Z₃` and `Z₄`
  -- which does not change the other variables. It retains independence, proving the conclusion.
  let phi_third : ∀ (i : Fin 3), (κ i → G) → G
    | 0 | 1 => (fun f ↦ f ⟨0, zero_lt_one⟩)
    | 2   => (fun f ↦ phi (f ⟨0, zero_lt_two⟩) (f ⟨1, one_lt_two⟩))
  convert T.comp phi_third ?_ with i
  · fin_cases i <;> rfl
  · intro i
    match i with
    | 0 | 1 => exact measurable_pi_apply _
    | 2 =>
      have : Measurable (fun (p : Fin 2 → G) ↦ (p 0, p 1)) := by fun_prop
      exact hphi.comp this
