import PFR.ForMathlib.Entropy.RuzsaDist
import Mathlib.Tactic.FunProp.Measurable

/-!
# More results about Ruzsa distance

More facts about Ruzsa distance and related inequalities, for use in the m-torsion version of PFR.

## Main definitions

## Main results

-/
section dataProcessing

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

namespace ProbabilityTheory

universe uΩ uS uT uU uV uW

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {W : Type uW} [mΩ : MeasurableSpace Ω]
  [Countable S] [Countable T] [Countable U] [Countable V] [Countable W]
  [Nonempty S] [Nonempty T] [Nonempty U] [Nonempty V] [Nonempty W]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace W]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U] [MeasurableSingletonClass V] [MeasurableSingletonClass W]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}

/--
Let `X, Y`be random variables. For any function `f, g` on the range of `X`, we have
`I[f(X) : Y] ≤ I[X : Y]`.
-/
lemma mutual_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) [FiniteRange X] [FiniteRange Y] :
    I[f ∘ X : Y ; μ] ≤ I[X : Y ; μ] := by
  have h_meas : Measurable (f ∘ X) := Measurable.comp (measurable_discrete f) hX
  rw [mutualInfo_comm h_meas hY, mutualInfo_comm hX hY,
    mutualInfo_eq_entropy_sub_condEntropy hY h_meas, mutualInfo_eq_entropy_sub_condEntropy hY hX]
  gcongr
  exact condEntropy_comp_ge μ hX hY f

/-- Let `X, Y` be random variables. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f ∘ X : g ∘ Y ; μ] ≤ I[X : Y ; μ]`. -/
lemma mutual_comp_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) (g : T → V) (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] :
    I[f ∘ X : g ∘ Y ; μ] ≤ I[X : Y ; μ] :=
  calc
    _ ≤ I[X : g ∘ Y ; μ] := mutual_comp_le μ hX (Measurable.comp hg hY) f
    _ = I[g ∘ Y : X ; μ] := mutualInfo_comm hX (Measurable.comp hg hY) μ
    _ ≤ I[Y : X ; μ] := mutual_comp_le μ hY hX g
    _ = I[X : Y ; μ] := mutualInfo_comm hY hX μ

/-- Let `X, Y, Z`. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ]`. -/
lemma condMutual_comp_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
  (hY : Measurable Y) (hZ : Measurable Z) (f : S → V) (g : T → W) (hg : Measurable g) [FiniteRange X]
  [FiniteRange Y] [FiniteRange Z] :
    I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  rw [condMutualInfo_eq_sum hZ, condMutualInfo_eq_sum hZ]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : 0 < (μ (Z ⁻¹' {i})).toReal
  · rw [mul_le_mul_left h]
    haveI : IsProbabilityMeasure (μ[|Z ← i]) := by
      apply cond_isProbabilityMeasure_of_finite
      · exact (ENNReal.toReal_ne_zero.mp (ne_of_gt h)).left
      . exact (ENNReal.toReal_ne_zero.mp (ne_of_gt h)).right
    apply mutual_comp_comp_le _ hX hY f g hg
  · suffices (μ (Z ⁻¹' {i})).toReal = 0 by simp only [this, zero_mul, le_refl]
    apply le_antisymm (le_of_not_lt h) ENNReal.toReal_nonneg

end ProbabilityTheory
end dataProcessing

open Filter Function MeasureTheory Measure ProbabilityTheory
open scoped BigOperators

attribute [symm] ProbabilityTheory.IdentDistrib.symm

variable {Ω Ω' Ω'' Ω''' G T : Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G]
  [Countable S] [Nonempty S] [MeasurableSpace S]
  [Countable T] [Nonempty T] [MeasurableSpace T]

variable {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G} [FiniteRange X] [FiniteRange Y] [FiniteRange Z]

/-`TODO`: we had to add the hp `Fintype G` to the following lemma in order to use `condIndep_copies`,
which requires it. Actually, we already have `FiniteRange X` and `FiniteRange Y`, so it should be
possible to remove it, or to gneralize the lemma to the case where `G` is not finite but the
random variables have finite range. One way to do it may be to write a lemma that tells us that
given a r.v., we can construct another r.v. that is identically distributed, which is defined the
immersion of the range of the initial r.v. inside the codomain (this would be a sort of canonical
version)-/

--PRed to Mathlib, see #13125. When we bump, remove this.
lemma ProbabilityTheory.indepFun_of_identDistrib_pair {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {μ' : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {X : Ω → α} {X' : Ω' → α} {Y : Ω → β} {Y' : Ω' → β} (hX : AEMeasurable X μ)
    (hX' : AEMeasurable X' μ') (hY : AEMeasurable Y μ) (hY' : AEMeasurable Y' μ')
    (h_indep : IndepFun X Y μ)
    (h_ident : IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (X' ω, Y' ω)) μ μ') :
    IndepFun X' Y' μ' := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hX' hY').mpr
  have iX : IdentDistrib X X' μ μ' := h_ident.comp measurable_fst
  have iY : IdentDistrib Y Y' μ μ' := h_ident.comp measurable_snd
  rw [← h_ident.map_eq, ← iX.map_eq, ← iY.map_eq]
  exact indepFun_iff_map_prod_eq_prod_map_map hX hY |>.mp h_indep

/--   If `X, Y` are `G`-valued, then `d[X;-Y] ≤ 3 d[X;Y]`. -/
lemma rdist_of_neg_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hX : Measurable X)
    (hY : Measurable Y) [Fintype G] :
    d[X ; μ # -Y ; μ'] ≤ 3 * d[X ; μ # Y ; μ'] := by
  obtain ⟨ν, X', Y', hν, mX', mY', h_indep', hXX', hYY'⟩ := independent_copies hX hY μ μ'
  rw [← IdentDistrib.rdist_eq hXX' hYY', ← IdentDistrib.rdist_eq hXX' (IdentDistrib.neg hYY')]
  obtain ⟨Ω₀, mΩ₀, XY'₁, XY'₂, Z', ν'₀, hν'₀, hXY'₁, hXY'₂, hZ', h_condIndep, h_id1sub, h_id2sub⟩
    := condIndep_copies (⟨X', Y'⟩) (X' - Y') (mX'.prod_mk mY') (mX'.sub' mY') ν
  let X'₁ := fun ω ↦ (XY'₁ ω).fst
  let Y'₁ := fun ω ↦ (XY'₁ ω).snd
  let X'₂ := fun ω ↦ (XY'₂ ω).fst
  let Y'₂ := fun ω ↦ (XY'₂ ω).snd
  have mX'₁ : Measurable X'₁ := by fun_prop
  have mY'₁ : Measurable Y'₁ := by fun_prop
  have Z'eq1 : Z' =ᵐ[ν'₀] X'₁ - Y'₁ :=
    (IdentDistrib.ae_snd h_id1sub.symm (measurableSet_discrete {x | x.2 = x.1.1 - x.1.2})
      (eventually_of_forall fun ω ↦ rfl) :)
  obtain ⟨ν₀, XY₁XY₂Z, XY₃, hν₀, hXY₁XY₂Z, hXY₃, h_indep, h_idXY₁XY₂Z, h_idXY₃⟩ :=
    independent_copies (hXY'₁.prod_mk hXY'₂ |>.prod_mk hZ') (mX'.prod_mk mY') ν'₀ ν
  let X₁ := fun ω ↦ (XY₁XY₂Z ω).fst.fst.fst
  let Y₁ := fun ω ↦ (XY₁XY₂Z ω).fst.fst.snd
  let X₂ := fun ω ↦ (XY₁XY₂Z ω).fst.snd.fst
  let Y₂ := fun ω ↦ (XY₁XY₂Z ω).fst.snd.snd
  let Z := fun ω ↦ (XY₁XY₂Z ω).snd
  let X₃ := fun ω ↦ (XY₃ ω).fst
  let Y₃ := fun ω ↦ (XY₃ ω).snd
  have mX₁ : Measurable X₁ := (by fun_prop)
  have mY₁ : Measurable Y₁ := (by fun_prop)
  have mX₂ : Measurable X₂ := (by fun_prop)
  have mY₂ : Measurable Y₂ := (by fun_prop)
  have mX₃ : Measurable X₃ := (by fun_prop)
  have mY₃ : Measurable Y₃ := (by fun_prop)
  have mZ : Measurable Z := (by fun_prop)
  have idXY₁Z : IdentDistrib (⟨⟨X₁, Y₁⟩, Z⟩) (⟨⟨X', Y'⟩, X' - Y'⟩) ν₀ ν :=
    h_idXY₁XY₂Z.comp (measurable_discrete fun x ↦ (x.1.1, x.2)) |>.trans h_id1sub
  have idXY₂Z : IdentDistrib (⟨⟨X₂, Y₂⟩, Z⟩) (⟨⟨X', Y'⟩, X' - Y'⟩) ν₀ ν :=
    h_idXY₁XY₂Z.comp (measurable_discrete fun x ↦ (x.1.2, x.2)) |>.trans h_id2sub
  have idXY₁ : IdentDistrib (⟨X₁, Y₁⟩) (⟨X', Y'⟩) ν₀ ν := by
    convert h_idXY₁XY₂Z.comp (measurable_discrete fun x ↦ x.1.1) |>.trans ?_
    exact h_id1sub.comp (measurable_discrete fun ((x, y), _) ↦ (x, y))
  have idXY₂ : IdentDistrib (⟨X₂, Y₂⟩) (⟨X', Y'⟩) ν₀ ν := by
    convert h_idXY₁XY₂Z.comp (measurable_discrete fun x ↦ x.1.2) |>.trans ?_
    exact h_id2sub.comp (measurable_discrete fun ((x, y), _) ↦ (x, y))
  have idXY₃ : IdentDistrib (⟨X₃, Y₃⟩) (⟨X', Y'⟩) ν₀ ν := h_idXY₃
  have idX₁ : IdentDistrib X₁ X' ν₀ ν := idXY₁.comp (by fun_prop)
  have idY₁ : IdentDistrib Y₁ Y' ν₀ ν := idXY₁.comp (by fun_prop)
  have idX₂ : IdentDistrib X₂ X' ν₀ ν := idXY₂.comp (by fun_prop)
  have idY₂ : IdentDistrib Y₂ Y' ν₀ ν := idXY₂.comp (by fun_prop)
  have idX₃ : IdentDistrib X₃ X' ν₀ ν := idXY₃.comp (by fun_prop)
  have idY₃ : IdentDistrib Y₃ Y' ν₀ ν := idXY₃.comp (by fun_prop)
  have idXY₁₂XY'₁₂ : IdentDistrib (⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩) (⟨⟨X'₁, Y'₁⟩, ⟨X'₂, Y'₂⟩⟩) ν₀ ν'₀ :=
    h_idXY₁XY₂Z.comp (measurable_discrete fun x ↦ x.1)
  have idXY₁ZXY'₁Z' : IdentDistrib (⟨⟨X₁, Y₁⟩, Z⟩) (⟨⟨X'₁, Y'₁⟩, Z'⟩) ν₀ ν'₀ :=
    h_idXY₁XY₂Z.comp (measurable_discrete fun x ↦ (x.1.1, x.2))
  have idXY₂ZXY'₂Z' : IdentDistrib (⟨⟨X₂, Y₂⟩, Z⟩) (⟨⟨X'₂, Y'₂⟩, Z'⟩) ν₀ ν'₀ :=
    h_idXY₁XY₂Z.comp (measurable_discrete fun x ↦ (x.1.2, x.2))
  have idZZ' : IdentDistrib Z Z' ν₀ ν'₀ := h_idXY₁XY₂Z.comp (measurable_discrete fun x ↦ x.2)
  have Zeq1 : Z =ᵐ[ν₀] X₁ - Y₁ := (IdentDistrib.ae_snd idXY₁Z.symm
      (measurableSet_discrete {x | x.2 = x.1.1 - x.1.2}) (eventually_of_forall fun ω ↦ rfl) :)
  have Zeq2 : Z =ᵐ[ν₀] X₂ - Y₂ :=
    (IdentDistrib.ae_snd idXY₂Z.symm (measurableSet_discrete {x | x.2 = x.1.1 - x.1.2})
      (eventually_of_forall fun ω ↦ rfl) :)
  have iX₁Y₃ : IndepFun X₁ Y₃ ν₀ := by
    convert h_indep.comp (measurable_discrete fun x ↦ x.1.1.1) (measurable_discrete fun x ↦ x.2)
  have iX₃Y₂ : IndepFun X₃ Y₂ ν₀ := by
    convert h_indep.symm.comp (measurable_discrete fun x ↦ x.1)
      (measurable_discrete fun x ↦ x.1.2.2)
  have iX₁Y₁ : IndepFun X₁ Y₁ ν₀ :=
    indepFun_of_identDistrib_pair mX'.aemeasurable mX₁.aemeasurable mY'.aemeasurable
      mY₁.aemeasurable h_indep' idXY₁.symm
  have iX₂Y₂ : IndepFun X₂ Y₂ ν₀ :=
    indepFun_of_identDistrib_pair mX'.aemeasurable mX₂.aemeasurable mY'.aemeasurable
      mY₂.aemeasurable h_indep' idXY₂.symm
  have iX₃Y₃ : IndepFun X₃ Y₃ ν₀ :=
    indepFun_of_identDistrib_pair mX'.aemeasurable mX₃.aemeasurable mY'.aemeasurable
      mY₃.aemeasurable h_indep' idXY₃.symm
  have iX₃negY₃ : IndepFun X₃ (-Y₃) ν₀ := iX₃Y₃.comp measurable_id measurable_neg
  have i112233 : IndepFun (⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩) (⟨X₃, Y₃⟩) ν₀ :=
    h_indep.comp (measurable_discrete fun (xy, _) ↦ xy) measurable_id
  have hX1 : H[X' ; ν] = H[X₁ ; ν₀] := idX₁.entropy_eq.symm
  have hX2 : H[X' ; ν] = H[X₂ ; ν₀] := idX₂.entropy_eq.symm
  have hX3 : H[X' ; ν] = H[X₃ ; ν₀] := idX₃.entropy_eq.symm
  have hY1 : H[Y' ; ν] = H[Y₁ ; ν₀] := idY₁.entropy_eq.symm
  have hY2 : H[Y' ; ν] = H[Y₂ ; ν₀] := idY₂.entropy_eq.symm
  have hY3 : H[Y' ; ν] = H[Y₃ ; ν₀] := idY₃.entropy_eq.symm
  have hnegY3 : H[Y₃ ; ν₀] = H[-Y₃ ; ν₀] := (entropy_neg mY₃).symm
  have hX1Y1 : H[⟨X₁, Y₁⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX1.symm ▸ hY1.symm ▸ (entropy_pair_eq_add mX₁ mY₁).mpr iX₁Y₁
  have hX2Y2 : H[⟨X₂, Y₂⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX2.symm ▸ hY2.symm ▸ (entropy_pair_eq_add mX₂ mY₂).mpr iX₂Y₂
  have hX3Y3 : H[⟨X₃, Y₃⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX3.symm ▸ hY3.symm ▸ (entropy_pair_eq_add mX₃ mY₃).mpr iX₃Y₃
  have dX3negY3 : d[X' ; ν # -Y' ; ν] = d[X₃ ; ν₀ # -Y₃ ; ν₀] := (idX₃.rdist_eq idY₃.neg).symm
  have dX1Y1 : d[X' ; ν # Y' ; ν] = d[X₁ ; ν₀ # Y₁ ; ν₀] := (idX₁.rdist_eq idY₁).symm
  have dX1Y3 : d[X' ; ν # Y' ; ν] = d[X₁ ; ν₀ # Y₃ ; ν₀] := (idX₁.rdist_eq idY₃).symm
  have dX3Y2 : d[X' ; ν # Y' ; ν] = d[X₃ ; ν₀ # Y₂ ; ν₀] := (idX₃.rdist_eq idY₂).symm
  have meas1321 : Measurable (⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩) := (mX₁.sub mY₃).prod_mk <| mX₂.prod_mk mY₁
  have meas321321 : Measurable (⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩) := (mX₃.sub mY₂).prod_mk meas1321
  have meas11 : Measurable (⟨X₁, Y₁⟩) := mX₁.prod_mk mY₁
  have meas22 : Measurable (⟨X₂, Y₂⟩) := mX₂.prod_mk mY₂
  have meas1122 : Measurable (⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩) := meas11.prod_mk meas22
  have meas33 : Measurable (⟨X₃, Y₃⟩) := mX₃.prod_mk mY₃
  have meas1neg1 : Measurable (X₁ - Y₁) := mX₁.sub mY₁
  have in1 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, ⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩⟩ ; ν₀] + H[X₃ + Y₃; ν₀]
      ≤ H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀] + H[⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩ ; ν₀] :=
    entropy_triple_add_entropy_le _ (by fun_prop) meas33 (mX₃.add mY₃)
  have eq2 : H[X₃ + Y₃; ν₀] = 1/2 * H[X'; ν] + 1/2 * H[Y'; ν] + d[X'; ν # -Y'; ν] := by
    rw [hX3, hY3, dX3negY3, hnegY3, IndepFun.rdist_eq iX₃negY₃ mX₃ mY₃.neg, sub_neg_eq_add]
    ring
  have eq3 : H[⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩ ; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX3Y3 ▸ entropy_of_comp_eq_of_comp ν₀ (meas33 |>.prod_mk <| mX₃.add mY₃) meas33
      (fun ((x3, y3), _) ↦ (x3, y3)) (fun (x3, y3) ↦ ((x3, y3), x3 + y3)) rfl rfl
  have eq4' : X₁ =ᵐ[ν₀] X₂ - Y₂ + Y₁ := by
    filter_upwards [Zeq1, Zeq2] with ω hZ hZ'
    simp only [Pi.add_apply, ← hZ', hZ, Pi.sub_apply, sub_add_cancel]
  have eq4 : X₃ + Y₃ =ᵐ[ν₀] (X₃ - Y₂) - (X₁ - Y₃) + X₂ + Y₁ := by
    filter_upwards [eq4'] with ω h
    simp only [Pi.add_apply, sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, Pi.neg_apply, h,
      add_left_neg, add_zero, neg_add_cancel_comm_assoc]
  have eq5 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀]
      = H[⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩ ; ν₀] :=
    calc
      _ = H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, (X₃ - Y₂) - (X₁ - Y₃) + X₂ + Y₁⟩ ; ν₀] := by
        refine IdentDistrib.entropy_eq <|
        IdentDistrib.of_ae_eq (meas321321.prod_mk <| mX₃.add mY₃).aemeasurable ?_
        filter_upwards [eq4] with ω h
        simp only [Prod.mk.injEq, h, Pi.add_apply, Pi.sub_apply, and_self]
      _ = _ := by
        refine entropy_of_comp_eq_of_comp ν₀
          (meas321321.prod_mk <| (((mX₃.sub mY₂).sub (mX₁.sub mY₃)).add mX₂).add mY₁) meas321321
          (fun ((x3y2, (x1y3, (x2, y1))), _) ↦ (x3y2, (x1y3, (x2, y1))))
          (fun (x3y2, (x1y3, (x2, y1))) ↦ ((x3y2, (x1y3, (x2, y1))), x3y2 - x1y3 + x2 + y1))
          rfl rfl
  have in6 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀]
      ≤ H[X₃ - Y₂; ν₀] + H[X₁ - Y₃; ν₀] + H[X₂; ν₀] + H[Y₁; ν₀] := by
    rw [eq5]
    refine (entropy_pair_le_add ?_ meas1321 ν₀).trans ?_
    · exact (mX₃.sub mY₂)
    simp only [add_assoc, add_le_add_iff_left]
    refine (entropy_pair_le_add ?_ ?_ ν₀).trans ?_
    · exact (mX₁.sub mY₃)
    · exact (mX₂.prod_mk mY₁)
    simp only [add_assoc, add_le_add_iff_left]
    exact entropy_pair_le_add mX₂ mY₁ ν₀
  have eq7 : H[X₃ - Y₂; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX3Y2, IndepFun.rdist_eq iX₃Y₂ mX₃ mY₂, hX3, hY2]
    ring_nf
  have eq8 : H[X₁ - Y₃; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX1Y3, IndepFun.rdist_eq iX₁Y₃ mX₁ mY₃, hX1, hY3]
    ring_nf
  have eq8' : H[X₁ - Y₁; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX1Y1, IndepFun.rdist_eq iX₁Y₁ mX₁ mY₁, hX1, hY1]
    ring_nf
  have in9 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀]
      ≤ 2 * H[X'; ν] + 2 * H[Y'; ν] + 2 * d[X'; ν # Y'; ν] := by
    rw [eq7, eq8, ← hX2, ← hY1] at in6
    ring_nf at in6 ⊢
    exact in6
  have in10 : H[⟨X₁, ⟨Y₁, ⟨X₂, ⟨Y₂, ⟨X₃, Y₃⟩⟩⟩⟩⟩ ; ν₀]
      ≤ H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, ⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩⟩ ; ν₀] := by
    convert entropy_comp_le ν₀
      (meas321321.prod_mk <| meas33.prod_mk <| mX₃.add mY₃)
      (fun ((x3y2, (x1y3, (x2, y1))), ((x3, y3), _))
        ↦ (x1y3 + y3, (y1, (x2, (x3 - x3y2, (x3, y3))))))
      <;> simp only [comp_apply, Pi.sub_apply, sub_add_cancel, sub_sub_cancel]
  have eq11 : H[⟨X₁, ⟨Y₁, ⟨X₂, ⟨Y₂, ⟨X₃, Y₃⟩⟩⟩⟩⟩ ; ν₀]
      = H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] + H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀]
        - H[X₁ - Y₁; ν₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
    calc
      _ = H[⟨⟨X'₁, Y'₁⟩, ⟨X'₂, Y'₂⟩⟩ ; ν'₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        rw [← idXY₁₂XY'₁₂.entropy_eq, ← (entropy_pair_eq_add meas1122 meas33).mpr i112233]
        exact entropy_of_comp_eq_of_comp ν₀
          (mX₁.prod_mk <| mY₁.prod_mk <| mX₂.prod_mk <| mY₂.prod_mk <| meas33)
          (meas1122.prod_mk meas33)
          (fun (x1, (y1, (x2, (y2, (x3, y3))))) ↦ (((x1, y1), (x2, y2)), (x3, y3)))
          (fun (((x1, y1), (x2, y2)), (x3, y3)) ↦ (x1, (y1, (x2, (y2, (x3, y3)))))) rfl rfl
      _ = H[⟨⟨X'₁, Y'₁⟩, ⟨⟨X'₂, Y'₂⟩, X'₁ - Y'₁⟩⟩ ; ν'₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 1
        exact entropy_of_comp_eq_of_comp ν'₀ (hXY'₁.prod_mk hXY'₂)
          (hXY'₁.prod_mk <| hXY'₂.prod_mk <| mX'₁.sub mY'₁)
          (fun ((x1, y1), (x2, y2)) ↦ ((x1, y1), ((x2, y2), x1 - y1)))
          (fun ((x1, y1), ((x2, y2), _)) ↦ ((x1, y1), (x2, y2))) rfl rfl
      _ = H[⟨⟨X'₁, Y'₁⟩, ⟨⟨X'₂, Y'₂⟩, Z'⟩⟩ ; ν'₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 1
        refine IdentDistrib.entropy_eq <| IdentDistrib.of_ae_eq
          (hXY'₁.prod_mk <| hXY'₂.prod_mk <| mX'₁.sub mY'₁).aemeasurable ?_
        filter_upwards [Z'eq1] with ω h
        simp only [Prod.mk.injEq, Pi.sub_apply, h, and_self]
      _ = H[⟨⟨X₁, Y₁⟩, Z⟩ ; ν₀] + H[⟨⟨X₂, Y₂⟩, Z⟩ ; ν₀] - H[Z ; ν₀]
          + H[⟨X₃, Y₃⟩ ; ν₀] := by
        rw [ent_of_cond_indep (μ := ν'₀) hXY'₁ hXY'₂ hZ' h_condIndep, idXY₁ZXY'₁Z'.entropy_eq,
          idXY₂ZXY'₂Z'.entropy_eq, idZZ'.entropy_eq]
      _ = H[⟨⟨X₁, Y₁⟩, X₁ - Y₁⟩ ; ν₀] + H[⟨⟨X₂, Y₂⟩, X₂ - Y₂⟩ ; ν₀] - H[X₁ - Y₁ ; ν₀]
          + H[⟨X₃, Y₃⟩ ; ν₀] := by
        rw [IdentDistrib.entropy_eq <| IdentDistrib.of_ae_eq mZ.aemeasurable Zeq1]
        congr 3
        · refine IdentDistrib.entropy_eq <| IdentDistrib.of_ae_eq
            (((mX₁.prod_mk mY₁).prod_mk mZ).aemeasurable) ?_
          filter_upwards [Zeq1] with ω h
          simp only [Prod.mk.injEq, h, Pi.sub_apply, and_self]
        · refine IdentDistrib.entropy_eq <| IdentDistrib.of_ae_eq
            ((mX₂.prod_mk mY₂).prod_mk mZ).aemeasurable ?_
          filter_upwards [Zeq2] with ω h
          simp only [Prod.mk.injEq, h, Pi.sub_apply, and_self]
      _ = H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] + H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀]
          - H[X₁ - Y₁; ν₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 3
        · exact entropy_of_comp_eq_of_comp ν₀ (meas11.prod_mk meas1neg1)
            (mX₁.prod_mk <| mY₁.prod_mk <| mX₁.sub mY₁)
            (fun ((x1, y1),x1y1) ↦ (x1, (y1, x1y1))) (fun (x1, (y1, x1y1)) ↦ ((x1, y1),x1y1))
            rfl rfl
        · exact entropy_of_comp_eq_of_comp ν₀ (meas22.prod_mk <| (mX₂).sub (mY₂))
            (mX₂.prod_mk <| mY₂.prod_mk <| mX₂.sub mY₂)
            (fun ((x1, y1),x1y1) ↦ (x1, (y1, x1y1))) (fun (x1, (y1, x1y1)) ↦ ((x1, y1),x1y1))
            rfl rfl
  have eq12_aux1 : H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] = H[⟨X₁, Y₁⟩ ; ν₀] :=
    entropy_of_comp_eq_of_comp ν₀
      (mX₁.prod_mk <| mY₁.prod_mk <| mX₁.sub mY₁) meas11
      (fun (x1, (y1, _)) ↦ (x1, y1)) (fun (x1, y1) ↦ (x1, (y1, x1 - y1))) rfl rfl
  have eq12_aux2 : H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀] = H[⟨X₂, Y₂⟩ ; ν₀] :=
    entropy_of_comp_eq_of_comp ν₀
      (mX₂.prod_mk <| mY₂.prod_mk <| mX₂.sub mY₂) meas22
      (fun (x1, (y1, _)) ↦ (x1, y1)) (fun (x1, y1) ↦ (x1, (y1, x1 - y1))) rfl rfl
  have eq12 : H[⟨X₁, ⟨Y₁, ⟨X₂, ⟨Y₂, ⟨X₃, Y₃⟩⟩⟩⟩⟩ ; ν₀]
      = 5/2 * (H[X'; ν] + H[Y'; ν]) - d[X'; ν # Y'; ν] := by
    rw [eq11, eq8', eq12_aux1, eq12_aux2, hX1Y1, hX2Y2, hX3Y3]
    ring_nf
  suffices h : 3 * (H[X'; ν] + H[Y'; ν]) - d[X'; ν # Y'; ν] + d[X'; ν # -Y'; ν]
      ≤ 3 * (H[X'; ν] + H[Y'; ν]) + 2 * d[X'; ν # Y'; ν] by
    simp only [sub_eq_add_neg, add_assoc, add_le_add_iff_left, neg_add_le_iff_le_add] at h
    ring_nf at h ⊢
    exact h
  calc
    _ = 5/2 * (H[X' ; ν] + H[Y' ; ν]) - d[X' ; ν # Y' ; ν]
        + 1/2 * (H[X' ; ν] + H[Y' ; ν]) + d[X' ; ν # -Y' ; ν] := by
      ring
    _ ≤ H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, ⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩⟩ ; ν₀]
        + 1/2 * (H[X' ; ν] + H[Y' ; ν]) + d[X' ; ν # -Y' ; ν] := by
      simp only [one_div, add_le_add_iff_right, eq12 ▸ in10]
    _ = H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, ⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩⟩ ; ν₀] + H[X₃ + Y₃ ; ν₀] := by
      simp only [one_div, eq2]
      ring
    _ ≤ H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀] + H[⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩ ; ν₀] := in1
    _ ≤ 2 * (H[X' ; ν] + H[Y' ; ν]) + 2 * d[X' ; ν # Y' ; ν] + H[⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩ ; ν₀] := by
      gcongr
      ring_nf at in9 ⊢
      simp only [in9]
    _ = 3 * (H[X' ; ν] + H[Y' ; ν]) + 2 * d[X' ; ν # Y' ; ν] := by
      simp only [eq3]
      ring

/--  If `n ≥ 1` and `X, Y₁, ..., Yₙ`$ are jointly independent `G`-valued random variables,
then `H[Y i₀ + ∑ i in s, Y i; μ ] - H[ Y i₀; μ ] ≤ ∑ i in s, (H[ Y i₀ + Y i; μ] - H[Y i₀; μ])`.
The spelling here is tentative.  Feel free to modify it to make the proof easier, or the application easier. -/
lemma kvm_ineq_I {I:Type*} {i₀: I} {s: Finset I} (hs: ¬ i₀ ∈ s) (Y: I → Ω → G) (hY: (i:I) → Measurable (Y i))
                 (hindep: iIndepFun (fun (i:I) => hG) Y μ )
                : H[ Y i₀ + ∑ i in s, Y i; μ ] - H[ Y i₀; μ ] ≤ ∑ i in s, (H[ Y i₀ + Y i; μ] - H[Y i₀; μ]) := by sorry

/--  If `n ≥ 1` and `X, Y₁, ..., Yₙ`$ are jointly independent `G`-valued random variables,
then `d[Y i₀; μ # ∑ i in s, Y i; μ ] ≤ 2 * ∑ i in s, d[Y i₀; μ # Y i; μ]`.
-/
lemma kvm_ineq_II {I:Type*} {i₀: I} {s: Finset I} (hs: ¬ i₀ ∈ s) (hs': Finset.Nonempty s) (Y: I → Ω → G)
                 (hY: (i:I) → Measurable (Y i)) (hindep: iIndepFun (fun (i:I) => hG) Y μ )
                : d[Y i₀; μ # ∑ i in s, Y i; μ ] ≤ 2 * ∑ i in s, d[Y i₀; μ # Y i; μ] := by sorry

/-- If `n ≥ 1` and `X, Y₁, ..., Yₙ`$ are jointly independent `G`-valued random variables,
then `d[Y i₀; μ # ∑ i in s, Y i; μ ] ≤ d[Y i₀; μ # Y i₁; μ] + (2:ℝ)⁻¹ * ∑ i in s, (H[Y i; μ] - H[Y i₁; μ])`.
-/
lemma kvm_ineq_III {I:Type*} {i₀ : I} {s: Finset I} (hs: ¬ i₀ ∈ s) (hs': Finset.Nonempty s) (Y: I → Ω → G)
                 (hY: (i:I) → Measurable (Y i)) (hindep: iIndepFun (fun (i:I) => hG) Y μ ) (i₁ : I)
                : d[Y i₀; μ # ∑ i in s, Y i; μ ] ≤ d[Y i₀; μ # Y i₁; μ] + (2:ℝ)⁻¹ * ∑ i in s, (H[Y i; μ] - H[Y i₁; μ]) := by sorry

open Classical in

/-- Let `X₁, ..., Xₘ` and `Y₁, ..., Yₗ` be tuples of jointly independent random variables (so the
`X`'s and `Y`'s are also independent of each other), and let `f: {1,..., l} → {1,... ,m}` be a
function, then  `H[∑ j, Y j] ≤ H[∑ i, X i] + ∑ j, H[Y j - X f(j)] - H[X_{f(j)}]`.-/
lemma ent_of_sum_le_ent_of_sum {I:Type*} {s t: Finset I} (hdisj: Disjoint s t) (hs: Finset.Nonempty s) (ht: Finset.Nonempty t) (X: I → Ω → G)
  (hX: (i:I) → Measurable (X i)) (hindep: iIndepFun (fun (i:I) => hG) X μ ) (f: I → I) (hf: Finset.image f t ⊆ s)
                : H[∑ i in t, X i; μ] ≤ H[∑ i in s, X i; μ] + ∑ i in t, (H[ X i - X (f i); μ] - H[X (f i); μ]) := by sorry

/-- Let `X,Y,X'` be independent `G`-valued random variables, with `X'` a copy of `X`,
and let `a` be an integer. Then `H[X - (a+1)Y] ≤ H[X - aY] + H[X - Y - X'] - H[X]` -/
lemma ent_of_sub_smul {Y : Ω → G} {X' : Ω → G} [FiniteRange Y] [FiniteRange X']
    [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (hindep: iIndepFun (fun _ ↦ hG) ![X, Y, X'] μ) (hident: IdentDistrib X X' μ μ) {a : ℤ} :
    H[X - (a+1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] := by
  rw [add_smul, one_smul, add_comm, sub_add_eq_sub_sub]
  have iX'Y : IndepFun X' Y μ := hindep.indepFun (show 2 ≠ 1 by simp)
  have iXY : IndepFun X Y μ := hindep.indepFun (show 0 ≠ 1 by simp)
  have hident' : IdentDistrib (X' - a • Y) (X - a • Y) μ μ := by
    simp_rw [sub_eq_add_neg]
    apply hident.symm.add (IdentDistrib.refl (hY.const_smul a).neg.aemeasurable)
    · convert iX'Y.comp measurable_id (measurable_discrete fun y ↦ -(a • y)) using 1
    · convert iXY.comp measurable_id (measurable_discrete fun y ↦ -(a • y)) using 1
  have iXY_X' : IndepFun (⟨X, Y⟩) X' μ :=
    hindep.indepFun_prod_mk (fun i ↦ (by fin_cases i <;> assumption)) 0 1 2
      (show 0 ≠ 2 by simp) (show 1 ≠ 2 by simp)
  calc
    _ ≤ H[X - Y - X' ; μ] + H[X' - a • Y ; μ] - H[X' ; μ] := by
      refine ent_of_diff_le _ _ _ (hX.sub hY) (hY.const_smul a) hX' ?_
      exact iXY_X'.comp (φ := fun (x, y) ↦ (x - y, a • y)) (measurable_discrete _) measurable_id
    _ = _ := by
      rw [hident.entropy_eq]
      simp only [add_comm, sub_left_inj, _root_.add_left_inj]
      exact hident'.entropy_eq

/-- Let `X,Y,X'` be independent `G`-valued random variables, with `X'` a copy of `X`,
and let `a` be an integer. Then `H[X - (a-1)Y] ≤ H[X - aY] + H[X - Y - X'] - H[X]` -/
lemma ent_of_sub_smul' {Y : Ω → G} {X' : Ω → G} [FiniteRange Y] [FiniteRange X']
    [IsProbabilityMeasure μ] (hX: Measurable X) (hY: Measurable Y) (hX': Measurable X')
    (hindep: iIndepFun (fun _ ↦ hG) ![X, Y, X'] μ) (hident: IdentDistrib X X' μ μ) {a : ℤ} :
    H[X - (a-1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] := by
  rw [sub_smul, one_smul, sub_eq_add_neg, neg_sub, add_sub]
  have iX'Y : IndepFun X' Y μ := hindep.indepFun (show 2 ≠ 1 by simp)
  have iXY : IndepFun X Y μ := hindep.indepFun (show 0 ≠ 1 by simp)
  have hident' : IdentDistrib (X' - a • Y) (X - a • Y) μ μ := by
    simp_rw [sub_eq_add_neg]
    apply hident.symm.add (IdentDistrib.refl (hY.const_smul a).neg.aemeasurable)
    · convert iX'Y.comp measurable_id (measurable_discrete fun y ↦ -(a • y)) using 1
    · convert iXY.comp measurable_id (measurable_discrete fun y ↦ -(a • y)) using 1
  have hident'' : IdentDistrib (-(X + Y - X')) (X - Y - X') μ μ := by
    simp_rw [neg_sub, ← sub_sub, sub_eq_add_neg, add_assoc]
    refine hident.symm.add ?_ ?_ ?_
    rotate_left
    . rw [← neg_add]
      apply IndepFun.comp _ measurable_id measurable_neg
      refine hindep.indepFun_add_right (fun i ↦ (by fin_cases i <;> assumption))
        2 0 1 (by simp) (by simp)
    . rw [← neg_add]
      apply IndepFun.comp _ measurable_id measurable_neg
      refine hindep.indepFun_add_right (fun i ↦ (by fin_cases i <;> assumption))
        0 1 2 (by simp) (by simp)
    rw [add_comm, ← neg_add, ← neg_add]
    exact (IdentDistrib.refl hY.aemeasurable).add hident iXY.symm iX'Y.symm |>.neg
  have iXY_X' : IndepFun (⟨X, Y⟩) X' μ :=
    hindep.indepFun_prod_mk (fun i ↦ (by fin_cases i <;> assumption)) 0 1 2
      (show 0 ≠ 2 by simp) (show 1 ≠ 2 by simp)
  calc
    _ ≤ H[X + Y - X' ; μ] + H[X' - a • Y ; μ] - H[X' ; μ] := by
      refine ent_of_diff_le _ _ _ (hX.add hY) (hY.const_smul a) hX' ?_
      exact iXY_X'.comp (φ := fun (x, y) ↦ (x + y, a • y)) (measurable_discrete _) measurable_id
    _ = H[- (X + Y - X') ; μ] + H[X - a • Y ; μ] - H[X ; μ] := by
      rw [hident.entropy_eq]
      simp only [hident'.entropy_eq, add_comm, sub_left_inj, _root_.add_right_inj]
      exact entropy_neg (hX.add hY |>.sub hX') |>.symm
    _ = _ := by
      rw [add_comm, hident''.entropy_eq]

/--  Let `X,Y` be independent `G`-valued random variables, and let `a` be an integer.  Then
  `H[X - aY] - H[X] ≤ 4 |a| d[X ; Y]`. -/
lemma ent_of_sub_smul_le {Y : Ω → G} [IsProbabilityMeasure μ] [Fintype G]
    (hX: Measurable X) (hY: Measurable Y) (hindep: IndepFun X Y μ) {a : ℤ} :
    H[X - a • Y; μ] - H[X; μ] ≤ 4 * |a| * d[X ; μ # Y ; μ] := by
  obtain ⟨Ω', mΩ', μ', X'₁, Y', X'₂, hμ', hindep', hX'₁, hY', hX'₂, idX₁, idY, idX₂⟩
    := independent_copies3_nondep hX hY hX  μ μ μ
  have iX₁Y : IndepFun X'₁ Y' μ' := hindep'.indepFun (show 0 ≠ 1 by simp)
  have iYX₂ : IndepFun Y' X'₂ μ' := hindep'.indepFun (show 1 ≠ 2 by simp)
  have iX₂nY : IndepFun X'₂ (-Y') μ' := iYX₂.symm.comp measurable_id measurable_neg
  have inX₁YX₂ : iIndepFun (fun _ ↦ hG) ![-X'₁, Y', X'₂] μ' := by
    convert hindep'.comp ![-id, id, id] (by measurability) with i
    match i with | 0 => rfl | 1 => rfl | 2 => rfl
  have idX₁X₂' : IdentDistrib X'₁ X'₂ μ' μ' := idX₁.trans idX₂.symm
  have idX₁Y : IdentDistrib (⟨X, Y⟩) (⟨X'₁, Y'⟩) μ μ' :=
    IdentDistrib.prod_mk idX₁.symm idY.symm hindep iX₁Y
  have h1 : H[Y' - X'₁ + X'₂; μ'] - H[Y' - X'₁; μ'] ≤ H[Y' + X'₂; μ'] - H[Y'; μ'] := by
    simp_rw [sub_eq_add_neg Y', add_comm Y' (-X'₁)]
    exact kaimanovich_vershik inX₁YX₂ hX'₁.neg hY' hX'₂
  have h2 : H[X'₁ - Y' - X'₂; μ'] - H[X'₁; μ'] ≤ d[X'₁ ; μ' # Y' ; μ'] + d[X'₁ ; μ' # -Y' ; μ'] := by
    rw [idX₁X₂'.rdist_eq (IdentDistrib.refl hY'.aemeasurable).neg, iX₁Y.rdist_eq hX'₁ hY',
      iX₂nY.rdist_eq hX'₂ hY'.neg, entropy_neg hY', idX₁X₂'.entropy_eq.symm]
    rw [show H[X'₁ - Y' - X'₂; μ'] = H[-(X'₁ - Y' - X'₂); μ']
      from entropy_neg (hX'₁.sub hY' |>.sub hX'₂) |>.symm]
    rw [show H[X'₁ - Y'; μ'] = H[-(X'₁ - Y'); μ'] from entropy_neg (hX'₁.sub hY') |>.symm]
    ring_nf
    rw [sub_eq_add_neg, add_comm, add_assoc, sub_neg_eq_add]
    gcongr
    convert sub_le_iff_le_add'.mp h1 using 1
    · simp [sub_eq_add_neg, add_comm]
    · simp only [sub_eq_add_neg, neg_add_rev, neg_neg, add_comm, add_assoc]
      linarith
  have h3 : H[X'₁ - Y' - X'₂ ; μ'] - H[X'₁; μ'] ≤ 4 * d[X'₁ ; μ' # Y' ; μ'] :=
    calc
      _ ≤ d[X'₁ ; μ' # Y' ; μ'] + d[X'₁ ; μ' # -Y' ; μ'] := h2
      _ ≤ d[X'₁ ; μ' # Y' ; μ'] + 3 * d[X'₁ ; μ' # Y' ; μ'] := by
        gcongr
        exact rdist_of_neg_le hX'₁ hY'
      _ = _ := by ring_nf
  have h4 (a : ℤ) : H[X - (a + 1) • Y; μ] ≤ H[X'₁ - a • Y'; μ'] + 4 * d[X'₁ ; μ' # Y' ; μ'] := by
    calc
      _ = H[X'₁ - (a + 1) • Y'; μ'] :=
        IdentDistrib.entropy_eq <|
          idX₁Y.comp (show Measurable (fun xy ↦ (xy.1 - (a + 1) • xy.2)) by fun_prop)
      _ ≤ H[X'₁ - a • Y'; μ'] + H[X'₁ - Y' - X'₂; μ'] - H[X'₁; μ'] :=
        ent_of_sub_smul hX'₁ hY' hX'₂ hindep' idX₁X₂'
      _ ≤ H[X'₁ - a • Y'; μ'] + 4 * d[X'₁ ; μ' # Y' ; μ'] := by
        rw [add_sub_assoc]
        gcongr
  have h4' (a : ℤ) : H[X - (a - 1) • Y; μ] ≤ H[X'₁ - a • Y'; μ'] + 4 * d[X'₁ ; μ' # Y' ; μ'] := by
    calc
      _ = H[X'₁ - (a - 1) • Y'; μ'] :=
        IdentDistrib.entropy_eq <|
          idX₁Y.comp (show Measurable (fun xy ↦ (xy.1 - (a - 1) • xy.2)) by fun_prop)
      _ ≤ H[X'₁ - a • Y'; μ'] + H[X'₁ - Y' - X'₂; μ'] - H[X'₁; μ'] :=
        ent_of_sub_smul' hX'₁ hY' hX'₂ hindep' idX₁X₂'
      _ ≤ H[X'₁ - a • Y'; μ'] + 4 * d[X'₁ ; μ' # Y' ; μ'] := by
        rw [add_sub_assoc]
        gcongr
  have (a : ℤ) : H[X'₁ - a • Y'; μ'] = H[X - a • Y; μ] :=
    idX₁Y.symm.comp (show Measurable (fun xy ↦ (xy.1 - a • xy.2)) by fun_prop) |>.entropy_eq
  simp_rw [IdentDistrib.rdist_eq idX₁ idY, this] at h4 h4'
  set! n := |a| with ha
  have hn : 0 ≤ n := by simp [ha]
  lift n to ℕ using hn with n
  induction' n with n ih generalizing a
  · rw [← ha, abs_eq_zero.mp ha.symm]
    simp
  · rename_i m _
    have : a ≠ 0 := by
      rw [ne_eq, ← abs_eq_zero, ← ha]
      exact NeZero.natCast_ne (m + 1) ℤ
    have : m = |a - 1| ∨ m = |a + 1| := by
      rcases lt_or_gt_of_ne this with h | h
      · right
        rw [abs_of_neg h] at ha
        rw [abs_of_nonpos (by exact h), neg_add, ← ha]
        norm_num
      · left
        rw [abs_of_pos h] at ha
        rw [abs_of_nonneg ?_, ← ha]
        swap; exact Int.sub_nonneg_of_le h
        norm_num
    rcases this with h | h
    · calc
        _ ≤ H[X - (a - 1) • Y; μ] - H[X; μ] + 4 * d[X ; μ # Y ; μ] := by
          nth_rw 1 [(a.sub_add_cancel 1).symm, sub_add_eq_add_sub _ H[X; μ]]
          gcongr
          exact h4 (a - 1)
        _ ≤ 4 * |a - 1| * d[X ; μ # Y ; μ] + 4 * d[X ; μ # Y ; μ] := by
          gcongr
          exact ih h h
        _ = 4 * |a| * d[X ; μ # Y ; μ] := by
          nth_rw 2 [← mul_one 4]
          rw [← add_mul, ← mul_add, ← ha, ← h]
          norm_num
    · calc
        _ ≤ H[X - (a + 1) • Y; μ] - H[X; μ] + 4 * d[X ; μ # Y ; μ] := by
          nth_rw 1 [(a.add_sub_cancel 1).symm, sub_add_eq_add_sub _ H[X; μ]]
          gcongr
          exact h4' (a + 1)
        _ ≤ 4 * |a + 1| * d[X ; μ # Y ; μ] + 4 * d[X ; μ # Y ; μ] := by
          gcongr
          exact ih h h
        _ = 4 * |a| * d[X ; μ # Y ; μ] := by
          nth_rw 2 [← mul_one 4]
          rw [← add_mul, ← mul_add, ← ha, ← h]
          norm_num

section multiDistance

open Filter Function MeasureTheory Measure ProbabilityTheory
open scoped BigOperators

variable {G : Type*}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G]

/--  Let `X_[m] = (X₁, ..., Xₘ)` be a non-empty finite tuple of `G`-valued random variables `X_i`.
Then we define `D[X_[m]] = H[∑ i, X_i'] - 1/m*∑ i, H[X_i']`, where the `X_i'` are independent copies
of the `X_i`.-/
noncomputable
def multiDist {m:ℕ} {Ω: Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (X : (i:Fin m) → (Ω i) → G) : ℝ := sorry

@[inherit_doc multiDist] notation3:max "D[" X " ; " hΩ "]" => multiDist hΩ X

/-- If `X_i` has the same distribution as `Y_i` for each `i`, then `D[X_[m]] = D[Y_[m]]`. -/
lemma multiDist_copy {m:ℕ} {Ω: Fin m → Type*} {Ω': Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (hΩ': (i:Fin m) → MeasureSpace (Ω' i)) (X : (i:Fin m) → (Ω i) → G) (X' : (i:Fin m) → (Ω' i) → G) (hident: ∀ i, IdentDistrib (X i) (X' i) (hΩ i).volume (hΩ' i).volume): D[ X ; hΩ ] = D[ X' ; hΩ' ] := by sorry

/-- If `X_i` are independent, then `D[X_[m]] = D[Y_[m]]`. -/
lemma multiDist_indep {m:ℕ} {Ω: Type*} (hΩ: MeasureSpace Ω)(X : Fin m → Ω → G) (hindep: iIndepFun (fun _ ↦ hG) X hΩ.volume) : D[ X ; fun _ ↦ hΩ ] = H[ ∑ i, X i ; hΩ.volume ] - (∑ i, H[ X i; hΩ.volume ]) / m := by sorry

/-- We have `D[X_[m]] ≥ 0`. -/
lemma multiDist_nonneg {m:ℕ} {Ω: Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (X : (i:Fin m) → (Ω i) → G) : D[ X ; hΩ ] ≥ 0 := by sorry

/--  If `φ : {1, ..., m} → {1, ...,m}` is a bijection, then `D[X_[m]] = D[(X_φ(1), ..., X_φ(m))]`-/
lemma multiDist_of_perm {m:ℕ} {Ω: Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (X : (i:Fin m) → (Ω i) → G) (φ: Equiv.Perm (Fin m)): D[ X ; hΩ ] = D[ fun i ↦ X (φ i); fun i ↦ hΩ (φ i)]:= by sorry

/-- Let `m ≥ 2`, and let `X_[m]` be a tuple of `G`-valued random variables. Then
  `∑ (1 \≤ j, k ≤ m, j ≠ k), d[X_j; -X_k] ≤ m(m-1) D[X_[m]].` -/
lemma multidist_ruzsa_I : 0 = 1 := by sorry

/-- Let `m ≥ 2`, and let `X_[m]` be a tuple of `G`-valued random variables. Then
  `∑ j, d[X_j;X_j] ≤ 2 m D[X_[m]]`. -/
lemma multidist_ruzsa_II : 0 = 1 := by sorry

/-- Let `I` be an indexing set of size `m ≥ 2`, and let `X_[m]` be a tuple of `G`-valued random
variables. If the `X_i` all have the same distribution, then `D[X_[m]] ≤ m d[X_i;X_i]` for any
`1 \≤ i ≤ m`. -/
lemma multidist_ruzsa_III : 0 = 1 := by sorry

/-- Let `I` be an indexing set of size `m ≥ 2`, and let `X_[m]` be a tuple of `G`-valued random
variables. Let `W := ∑ (i ∈ I) X_i`. Then `d[W;-W] ≤ 2 D[X_i]`. -/
lemma multidist_ruzsa_IV : 0 = 1 := by sorry

/-- If `D[X_[m]]=0`, then for each `i ∈ I` there is a finite subgroup `H_i ≤ G` such that
`d[X_i; U_{H_i}] = 0`. -/
lemma multidist_eq_zero : 0 = 1 := by sorry

/-- If `X_[m] = (X_1, ..., X_m)` and `Y_[m] = (Y_1, ..., Y_m)` are tuples of random variables,
with the `X_i` being `G`-valued (but the `Y_i` need not be), then we define
`D[X_[m] | Y_[m]] := H[∑ i, X_i | (Y_1, ..., Y_m)] - 1/m * ∑ i, H[X_i' | Y_i']`
where `(X_i', Y_i)`, `1 ≤ i ≤ m` are independent copies of `(X_i,Y_i), 1 ≤ i ≤ m` (but note here
that we do *not* assume `X_i` are independent of `Y_i`, or `X_i'` independent of `Y_i`. -/
noncomputable
def condMultiDist {m:ℕ} {Ω: Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (X : (i:Fin m) → (Ω i) → G) (Y : (i:Fin m) → (Ω i) → G) : ℝ := sorry

@[inherit_doc multiDist] notation3:max "D[" X " | " Y " ; " hΩ "]" => condMultiDist hΩ X Y

/-- With the above notation, we have
  \begin{equation}\label{multi-def-cond-alt}
    D[ X_[m] | Y_[m]] = \sum_{(y_i)_{1 \leq i \leq m}} \biggl(\prod_{1 \leq i \leq m} p_{Y_i}(y_i)\biggr) D[ (X_i \,|\, Y_i \mathop{=}y_i)_{1 \leq i \leq m}]
  \end{equation}
  where each `y_i` ranges over the support of `p_{Y_i}` for `1 ≤ i ≤ m`. -/
lemma condMultiDist_eq : 0 = 1 := by sorry

end multiDistance

section multiDistance_chainRule

/-- Let `π : G → H` be a homomorphism of abelian groups and let `X_[m]` be a tuple of jointly
independent `G`-valued random variables. Then `D[X_[m]]` is equal to
`D[X_[m] | π(X_[m])] + D[π(X_[m])] + I[∑ i, X_i : π(X_[m]) ; | ; π(∑ i, X_i)]`
where `\pi(X_[m]) := (π(X_1), ..., π(X_m))`.
-/
lemma multiDist_chainRule : 0 = 1 := by sorry

/-- Let `π : G → H` be a homomorphism of abelian groups. Let `I` be a finite index set and let
`X_[m]` be a tuple of `G`-valued random variables. Let `Y_[m]` be another tuple of random variables
(not necessarily `G`-valued). Suppose that the pairs `(X_i, Y_i)` are jointly independent of one
another (but `X_i` need not be independent of `Y_i`). Then
`D[X_[m] | Y_[m]] = D[X_[m] ,|, π(X_[m]), Y_[m]] + D[π(X_[m]) ,| , Y_[m]]`
`+ I[∑ i, X_i : π(X_[m]) ; | ;  π(∑ i, X_i), Y_[m] ]`. -/
lemma cond_multiDist_chainRule : 0 = 1 := by sorry

/-- Let `m` be a positive integer. Suppose one has a sequence `G_m → G_{m-1} → ... → G_1 → G_0 = {0}`
of homomorphisms between abelian groups `G_0, ...,G_m`, and for each `d=0, ...,m`, let
`π_d : G_m → G_d` be the homomorphism from `G_m` to `G_d` arising from this sequence by composition
(so for instance `π_m` is the identity homomorphism and `π_0` is the zero homomorphism).
Let `X_[m] = (X_1, ..., X_m)` be a jointly independent tuple of `G_m`-valued random variables.
Then `D[X_[m]] = ∑ d, D[π_d(X_[m]) ,| , π_(d-1)(X_[m])]`
` + ∑ (d=1, ..., m-1), I[∑ i, X_i : π_d(X_[m]) | π_d(∑ i, X_i), π_(d-1})(X_[m])]`.-/
lemma iter_multiDist_chainRule : 0 = 1 := by sorry

/--Under the preceding hypotheses,
`D[ X_[m]] ≥ ∑ d, D[πd(X_[m])| π_(d-1})(X_[m])] + I[∑ i, X_i : π_1(X_[m]) | π_1(∑ i, X_i)]`. -/
lemma iter_multiDist_chainRule' : 0 = 1 := by sorry

/-- Let `G` be an abelian group and let `m ≥ 2`. Suppose that `X_{i,j}`, `1 ≤ i, j ≤ m`, are
independent `G`-valued random variables. Then
`I[ (∑ i, X_{i,j})_j =1}^{m} : \bigl(\sum_{j=1}^m X_{i,j}\bigr)_{i = 1}^m \; \big| \; \sum_{i=1}^m \sum_{j = 1}^m  X_{i,j} ] $$
  is less than
  $$\sum_{j=1}^{m-1} \Bigl(D[(X_{i, j})_{i = 1}^m] - D[ (X_{i, j})_{i = 1}^m  \; \big| \; (X_{i,j} + \cdots + X_{i,m})_{i =1}^m ]\Bigr)$$
  $$+  D[(X_{i,m})_{i=1}^m] - D[ \bigl(\sum_{j=1}^m X_{i,j}\bigr)_{i=1}^m ],$$
  where all the multidistances here involve the indexing set $\{1,\dots, m\}$.
  -/
lemma cor_multiDist_chainRule : 0 = 1 := by sorry


end multiDistance_chainRule
