import PFR.ForMathlib.Entropy.Basic
import PFR.ForMathlib.Entropy.Kernel.Group

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory

universe uΩ uS uT uU
variable {Ω : Type uΩ} {G : Type uS} {T : Type uT} {U : Type uU} [mΩ : MeasurableSpace Ω]
  [Countable G] [Countable T] [Countable U]
  [hG : MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass G] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Group G] {X Y : Ω → G} {μ : Measure Ω}

namespace ProbabilityTheory
section entropy

@[to_additive (attr := simp)]
lemma entropy_mul_const (hX : Measurable X) (c : G) :
    H[X * fun _ ↦ c; μ] = H[X ; μ] := by
  apply entropy_comp_of_injective μ hX _ $ mul_left_injective c

/-- `H[X, X * Y] = H[X, Y]`. -/
@[to_additive "`H[X, X + Y] = H[X, Y]`"]
lemma entropy_mul_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, X * Y⟩; μ] = H[⟨X, Y⟩ ; μ] := by
  change H[(Equiv.refl _).prodShear Equiv.mulLeft ∘ ⟨X, Y⟩ ; μ] = H[⟨X, Y⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ $ Equiv.injective _

/-- `H[X, Y * X] = H[X, Y]` -/
@[to_additive "`H[X, Y + X] = H[X, Y]`"]
lemma entropy_mul_right' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, Y * X⟩; μ] = H[⟨X, Y⟩ ; μ] := by
  change H[(Equiv.refl _).prodShear Equiv.mulRight ∘ ⟨X, Y⟩ ; μ] = H[⟨X, Y⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ $ Equiv.injective _

/-- `H[Y * X, Y] = H[X, Y]` -/
@[to_additive "`H[Y + X, Y] = H[X, Y]`"]
lemma entropy_mul_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨Y * X, Y⟩; μ] = H[⟨X, Y⟩ ; μ] :=
  (entropy_comm (hY.mul hX) hY _).trans $ (entropy_mul_right hY hX _).trans $ entropy_comm hY hX _

/-- `H[X * Y, Y] = H[X, Y]` -/
@[to_additive "`H[X + Y, Y] = H[X, Y]`"]
lemma entropy_mul_left' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X * Y, Y⟩; μ] = H[⟨X, Y⟩ ; μ] :=
  (entropy_comm (hX.mul hY) hY _).trans $ (entropy_mul_right' hY hX _).trans $ entropy_comm hY hX _

/-- `H[X, Y⁻¹] = H[X, Y]` -/
@[to_additive "`H[X, -Y] = H[X, Y]`"]
lemma entropy_inv_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, Y⁻¹⟩; μ] = H[⟨X, Y⟩ ; μ] := by
  change H[(Equiv.refl _).prodCongr (Equiv.inv _) ∘ ⟨X, Y⟩ ; μ] = H[⟨X, Y⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)

/-- `H[X⁻¹, Y] = H[X, Y]` -/
@[to_additive "`H[-X, Y] = H[X, Y]`"]
lemma entropy_inv_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X⁻¹, Y⟩; μ] = H[⟨X, Y⟩ ; μ] := by
  change H[(Equiv.inv _).prodCongr (Equiv.refl _) ∘ ⟨X, Y⟩ ; μ] = H[⟨X, Y⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)

/-- `H[X, X / Y] = H[X, Y]` -/
@[to_additive "`H[X, X - Y] = H[X, Y]`"]
lemma entropy_div_right (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, X / Y⟩; μ] = H[⟨X, Y⟩ ; μ] := by
  change H[(Equiv.refl _).prodShear Equiv.divLeft ∘ ⟨X, Y⟩ ; μ] = H[⟨X, Y⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)

/-- `H[X, Y / X] = H[X, Y]` -/
@[to_additive "`H[X, Y - X] = H[X, Y]`"]
lemma entropy_div_right' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, Y / X⟩; μ] = H[⟨X, Y⟩ ; μ] := by
  change H[(Equiv.refl _).prodShear Equiv.divRight ∘ ⟨X, Y⟩ ; μ] = H[⟨X, Y⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prodMk hY) _ (Equiv.injective _)

/-- `H[Y / X, Y] = H[X, Y]` -/
@[to_additive "`H[Y - X, Y] = H[X, Y]`"]
lemma entropy_div_left (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨Y / X, Y⟩; μ] = H[⟨X, Y⟩ ; μ] :=
  (entropy_comm (hY.div hX) hY _).trans $ (entropy_div_right hY hX _).trans $ entropy_comm hY hX _

/-- `H[X / Y, Y] = H[X, Y]` -/
@[to_additive "`H[X - Y, Y] = H[X, Y]`"]
lemma entropy_div_left' (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X / Y, Y⟩; μ] = H[⟨X, Y⟩ ; μ] :=
  (entropy_comm (hX.div hY) hY _).trans $ (entropy_div_right' hY hX _).trans $ entropy_comm hY hX _

/-- If `X` is `G`-valued, then `H[X⁻¹]=H[X]`. -/
@[to_additive "If `X` is `G`-valued, then `H[-X]=H[X]`."]
lemma entropy_inv (hX : Measurable X) : H[X⁻¹ ; μ] = H[X ; μ] :=
  entropy_comp_of_injective μ hX (·⁻¹) inv_injective

/-- `H[X / Y] = H[Y / X]` -/
@[to_additive "`H[X - Y] = H[Y - X]`"]
lemma entropy_div_comm {Y : Ω → G} (hX : Measurable X) (hY : Measurable Y) :
    H[X / Y ; μ] = H[Y / X ; μ] := by rw [← inv_div]; exact entropy_inv (hY.div hX)


/-- `max(H[X | Z], H[Y | Z]) - I[X : Y | Z] ≤ H[X / Y | Z]` -/
@[to_additive "`max(H[X | Z], H[Y | Z]) - I[X : Y | Z] ≤ H[X - Y | Z]`"]
lemma max_condEntropy_sub_condMutualInfo_le_condEntropy_div [FiniteRange X] [FiniteRange Y]
    {Z : Ω → T} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsProbabilityMeasure μ] [FiniteRange Z] :
    (max H[X | Z ; μ] H[Y | Z ; μ]) - I[X : Y | Z ; μ] ≤ H[X / Y | Z ; μ] := by
  rw [condMutualInfo_comm hX hY, condEntropy_eq_kernel_entropy hX hZ,
    condEntropy_eq_kernel_entropy hY hZ, condMutualInfo_eq_kernel_mutualInfo hY hX hZ,
    condEntropy_eq_kernel_entropy ?_ hZ]
  swap ; · exact hX.div hY
  rw [Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ μ).symm,
    Kernel.entropy_congr (condDistrib_fst_ae_eq hY hX hZ μ).symm, max_comm]
  refine (Kernel.max_entropy_sub_mutualInfo_le_entropy_div _ _ ?_).trans_eq ?_
  · exact Kernel.aefiniteKernelSupport_condDistrib _ _ _ (hY.prodMk hX) hZ
  rw [Kernel.entropy_div_comm]
  have h := condDistrib_comp (hY.prodMk hX) hZ μ (fun x ↦ x.2 / x.1)
  rw [Kernel.entropy_congr h.symm]
  rfl

end entropy

section condEntropy
variable [IsFiniteMeasure μ] [FiniteRange Y]

/-- `H[Y * X | Y] = H[X | Y]` -/
@[to_additive "`H[Y + X | Y] = H[X | Y]`"]
lemma condEntropy_mul_left (hX : Measurable X) (hY : Measurable Y) :
     H[Y * X | Y ; μ] = H[X | Y ; μ] :=
  condEntropy_of_injective μ hX hY (fun y x ↦ y * x) mul_right_injective

/-- `H[X * Y | Y] = H[X | Y]` -/
@[to_additive "`H[X + Y | Y] = H[X | Y]`"]
lemma condEntropy_mul_right (hX : Measurable X) (hY : Measurable Y) :
    H[X * Y | Y ; μ] = H[X | Y ; μ] :=
  condEntropy_of_injective μ hX hY (fun y x ↦ x * y) mul_left_injective

/-- `H[Y / X | Y] = H[X | Y]` -/
@[to_additive "`H[Y - X | Y] = H[X | Y]`"]
lemma condEntropy_div_left (hX : Measurable X) (hY : Measurable Y) :
    H[Y / X | Y ; μ] = H[X | Y ; μ] :=
  condEntropy_of_injective μ hX hY (fun y x ↦ y / x) fun _ ↦ div_right_injective

/-- `H[X / Y | Y] = H[X | Y]` -/
@[to_additive "`H[X - Y | Y] = H[X | Y]`"]
lemma condEntropy_div_right (hX : Measurable X) (hY : Measurable Y) :
    H[X / Y | Y ; μ] = H[X | Y ; μ] :=
  condEntropy_of_injective μ hX hY (fun y x ↦ x / y) fun _ ↦ div_left_injective

end condEntropy

section mutualInfo

variable [FiniteRange X] [FiniteRange Y]

/-- `I[X : X * Y] = H[X * Y] - H[Y]` iff `X, Y` are independent. -/
@[to_additive "`I[X : X + Y] = H[X + Y] - H[Y]` iff `X, Y` are independent."]
lemma mutualInfo_mul_right (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h : IndepFun X Y μ) :
    I[X : X * Y ; μ] = H[X * Y ; μ] - H[Y ; μ] := by
  rw [mutualInfo_def, entropy_mul_right hX hY, h.entropy_pair_eq_add hX hY]
  abel

end mutualInfo

section IsProbabilityMeasure
variable [IsProbabilityMeasure μ] {Y : Ω → G} [FiniteRange X] [FiniteRange Y]

/-- `H[X] - I[X : Y] ≤ H[X * Y]` -/
@[to_additive "`H[X] - I[X : Y] ≤ H[X + Y]`"]
lemma entropy_sub_mutualInfo_le_entropy_mul (hX : Measurable X) (hY : Measurable Y) :
    H[X ; μ] - I[X : Y ; μ] ≤ H[X * Y ; μ] := by
  rw [entropy_sub_mutualInfo_eq_condEntropy hX hY, ← condEntropy_mul_right hX hY]
  exact condEntropy_le_entropy _ (hX.mul hY) hY

/-- `H[Y] - I[X : Y] ≤ H[X * Y]` -/
@[to_additive "`H[Y] - I[X : Y] ≤ H[X + Y]`"]
lemma entropy_sub_mutualInfo_le_entropy_mul' (hX : Measurable X) (hY : Measurable Y) :
    H[Y ; μ] - I[X : Y ; μ] ≤ H[X * Y ; μ] := by
  rw [entropy_sub_mutualInfo_eq_condEntropy' hX hY, ← condEntropy_mul_left hY hX]
  exact condEntropy_le_entropy _ (hX.mul hY) hX

/-- `H[X] - I[X : Y] ≤ H[X / Y]` -/
@[to_additive "`H[X] - I[X : Y] ≤ H[X - Y]`"]
lemma entropy_sub_mutualInfo_le_entropy_div (hX : Measurable X) (hY : Measurable Y) :
    H[X ; μ] - I[X : Y ; μ] ≤ H[X / Y ; μ] := by
  rw [entropy_sub_mutualInfo_eq_condEntropy hX hY, ← condEntropy_div_right hX hY]
  exact condEntropy_le_entropy _ (hX.div hY) hY

/-- `H[Y] - I[X : Y] ≤ H[X / Y]` -/
@[to_additive "`H[Y] - I[X : Y] ≤ H[X - Y]`"]
lemma entropy_sub_mutualInfo_le_entropy_div' (hX : Measurable X) (hY : Measurable Y) :
    H[Y ; μ] - I[X : Y ; μ] ≤ H[X / Y ; μ] := by
  rw [mutualInfo_comm hX hY, entropy_sub_mutualInfo_eq_condEntropy hY hX,
    ← condEntropy_div_left hY hX]
  exact condEntropy_le_entropy _ (hX.div hY) hX

/-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X * Y]` -/
@[to_additive "`max(H[X], H[Y]) - I[X : Y] ≤ H[X + Y]`"]
lemma max_entropy_sub_mutualInfo_le_entropy_mul (hX : Measurable X) (hY : Measurable Y) :
    max H[X ; μ] H[Y ; μ] - I[X : Y ; μ] ≤ H[X * Y ; μ] := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_sub_mutualInfo_le_entropy_mul hX hY, entropy_sub_mutualInfo_le_entropy_mul' hX hY⟩

/-- `max(H[X], H[Y]) - I[X : Y] ≤ H[X / Y]` -/
@[to_additive "`max(H[X], H[Y]) - I[X : Y] ≤ H[X - Y]`"]
lemma max_entropy_sub_mutualInfo_le_entropy_div (hX : Measurable X) (hY : Measurable Y) :
    max H[X ; μ] H[Y ; μ] - I[X : Y ; μ] ≤ H[X / Y ; μ] := by
  rw [← max_sub_sub_right, max_le_iff]
  exact ⟨entropy_sub_mutualInfo_le_entropy_div hX hY, entropy_sub_mutualInfo_le_entropy_div' hX hY⟩

/-- `max(H[X | Z], H[Y | Z]) - I[X : Y | Z] ≤ H[X * Y | Z]` -/
@[to_additive "`max(H[X | Z], H[Y | Z]) - I[X : Y | Z] ≤ H[X + Y | Z]`"]
lemma max_condEntropy_sub_condMutualInfo_le_condEntropy_mul {Z : Ω → T} [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    max H[X | Z ; μ] H[Y | Z ; μ] - I[X : Y | Z ; μ] ≤ H[X * Y | Z ; μ] := by
  rw [condMutualInfo_comm hX hY, condEntropy_eq_kernel_entropy hX hZ,
    condEntropy_eq_kernel_entropy hY hZ, condMutualInfo_eq_kernel_mutualInfo hY hX hZ,
    condEntropy_eq_kernel_entropy (show Measurable (X * Y) from hX.mul hY) hZ]
  rw [Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ μ).symm,
    Kernel.entropy_congr (condDistrib_fst_ae_eq hY hX hZ μ).symm,
    max_comm]
  refine (Kernel.max_entropy_sub_mutualInfo_le_entropy_mul' _ _ ?_).trans_eq ?_
  · exact Kernel.aefiniteKernelSupport_condDistrib _ _ _ (hY.prodMk hX) hZ
  have h := condDistrib_comp (hY.prodMk hX) hZ μ (fun x ↦ x.2 * x.1)
  rw [Kernel.entropy_congr h.symm]
  rfl


/-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X * Y]`. -/
@[to_additive "If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X + Y]`"]
lemma max_entropy_le_entropy_mul (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) :
    max H[X ; μ] H[Y ; μ] ≤ H[X * Y ; μ] := by
  simpa [h.mutualInfo_eq_zero hX hY] using max_entropy_sub_mutualInfo_le_entropy_mul hX hY (μ := μ)

/-- If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X / Y]`. -/
@[to_additive "If `X, Y` are independent, then `max(H[X], H[Y]) ≤ H[X - Y]`."]
lemma max_entropy_le_entropy_div (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y μ) :
    max H[X ; μ] H[Y ; μ] ≤ H[X / Y ; μ] := by
  simpa [h.mutualInfo_eq_zero hX hY] using max_entropy_sub_mutualInfo_le_entropy_div hX hY (μ := μ)

/-- If `X₁, ..., Xₙ` are independent and `s ⊆ {1, ..., n}`, then for all `i ∈ s`,
`H[Xᵢ] ≤ H[∏ j ∈ s, Xⱼ]`. -/
@[to_additive "If `X₁, ..., Xₙ` are independent and `s ⊆ {1, ..., n}`, then for all `i ∈ s`,
`H[Xᵢ] ≤ H[∑ j ∈ s, Xⱼ]`."]
lemma max_entropy_le_entropy_prod {G : Type*} [Countable G] [hG : MeasurableSpace G]
    [MeasurableSingletonClass G] [CommGroup G] [MeasurableMul₂ G]
    {I : Type*} {s : Finset I} {i₀ : I} (hi₀ : i₀ ∈ s) {X : I → Ω → G} [∀ i, FiniteRange (X i)]
    (hX : (i : I) → Measurable (X i)) (h_indep : iIndepFun X μ) :
    H[X i₀ ; μ] ≤ H[∏ i ∈ s, X i ; μ] := by
  have hs : s.Nonempty := ⟨i₀, hi₀⟩
  induction' hs using Finset.Nonempty.cons_induction with i j s Hnot _ Hind
  · simp_all
  · rw [Finset.prod_cons]
    rcases Finset.mem_cons.mp hi₀ with rfl | hi₀
    · calc
        _ ≤ max H[X i₀ ; μ] H[∏ i ∈ s, X i ; μ] := le_max_left _ _
        _ ≤ H[X i₀ * ∏ i ∈ s, X i ; μ] := by
          refine max_entropy_le_entropy_mul (hX i₀) (by fun_prop) ?_
          exact iIndepFun.indepFun_finset_prod_of_notMem h_indep hX Hnot |>.symm
    · calc
        _ ≤ H[∏ i ∈ s, X i ; μ] := Hind hi₀
        _ ≤ max H[X j ; μ] H[∏ i ∈ s, X i ; μ] := le_max_right _ _
        _ ≤ H[X j * ∏ x ∈ s, X x ; μ] := by
          refine max_entropy_le_entropy_mul (hX j) (by fun_prop) ?_
          exact iIndepFun.indepFun_finset_prod_of_notMem h_indep hX Hnot |>.symm

end IsProbabilityMeasure
end ProbabilityTheory
