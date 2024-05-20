import PFR.ForMathlib.Entropy.RuzsaDist

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

/--
 Let `X,Y` be random variables. For any functions `f, g` on the ranges of `X, Y` respectively, we
 have `I[f(X) : g(Y)] \leq I[X : Y]`.
 -/
lemma mutual_comp_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (f : S → U) (g : T → V) (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] :
    I[f ∘ X : g ∘ Y ; μ] ≤ I[X : Y ; μ] :=
  calc
    _ ≤ I[X : g ∘ Y ; μ] := mutual_comp_le μ hX (Measurable.comp hg hY) f
    _ = I[g ∘ Y : X ; μ] := mutualInfo_comm hX (Measurable.comp hg hY) μ
    _ ≤ I[Y : X ; μ] := mutual_comp_le μ hY hX g
    _ = I[X : Y ; μ] := mutualInfo_comm hY hX μ

/--
Let `X,Y,Z`. For any functions `f, g` on the ranges of `X, Y` respectively,
we have `I[f(X) : g(Y)|Z] ≤ I[X :Y |Z]`.
-/
lemma condMutual_comp_comp_le (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X)
  (hY : Measurable Y) (hZ : Measurable Z) (f : S → V) (g : T → W) [FiniteRange X] [FiniteRange Y]:
    I[f ∘ X : g ∘ Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by sorry

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

#check IdentDistrib.ae_snd
#check independent_copies
/--   If `X, Y` are `G`-valued, then `d[X;-Y] ≤ 3 d[X;Y]`. -/
lemma rdist_of_neg_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hX : Measurable X)
    (hY : Measurable Y) [Fintype G] :
    d[X ; μ # -Y ; μ'] ≤ 3 * d[X ; μ # Y ; μ'] := by
  obtain ⟨ν, X', Y', hν, hX', hY', h_indep', hXX', hYY'⟩ := independent_copies hX hY μ μ'
  rw [← IdentDistrib.rdist_eq hXX' hYY', ← IdentDistrib.rdist_eq hXX' (IdentDistrib.neg hYY')]

  obtain ⟨Ω₀, mΩ₀, XY'₁, XY'₂, Z', ν'₀, hν'₀, hXY'₁, hXY'₂, hZ', h_indep12sub, h_id1sub, h_id2sub⟩
    := condIndep_copies (⟨X', Y'⟩) (X' - Y') (hX'.prod_mk hY') (hX'.sub' hY') ν
  let X'₁ := fun ω ↦ (XY'₁ ω).fst
  let Y'₁ := fun ω ↦ (XY'₁ ω).snd
  let X'₂ := fun ω ↦ (XY'₂ ω).fst
  let Y'₂ := fun ω ↦ (XY'₂ ω).snd
  -- have Zeq1 : Z =ᵐ[ν₀] X₁ - Y₁ := by
  --   sorry
  -- have Zeq2 : Z =ᵐ[ν₀] X₂ - Y₂ := by
  --   sorry

  -- have hidX₁ : IdentDistrib X₁ X' ν₀ ν := by
  --   exact h_id1sub.comp (measurable_discrete (fun ((x,y), z) ↦ x))
  -- have hidY₁ : IdentDistrib Y₁ Y' ν₀ ν := by
  --   exact h_id1sub.comp (measurable_discrete (fun ((x,y), z) ↦ y))
  -- have hidX₂ : IdentDistrib X₂ X' ν₀ ν := by
  --   exact h_id2sub.comp (measurable_discrete (fun ((x,y), z) ↦ x))
  -- have hidY₂ : IdentDistrib Y₂ Y' ν₀ ν := by
  --   exact h_id2sub.comp (measurable_discrete (fun ((x,y), z) ↦ y))

  obtain ⟨ν₀, XY₁XY₂Z, XY₃, hν₀, hXY₁XY₂Z, hXY₃, h_indep, h_idXY₁XY₂Z, h_idXY₃⟩ :=
    independent_copies (hXY'₁.prod_mk hXY'₂ |>.prod_mk hZ') (hX'.prod_mk hY') ν'₀ ν

  let X₁ := fun ω ↦ (XY₁XY₂Z ω).fst.fst.fst
  let Y₁ := fun ω ↦ (XY₁XY₂Z ω).fst.fst.snd
  let X₂ := fun ω ↦ (XY₁XY₂Z ω).fst.snd.fst
  let Y₂ := fun ω ↦ (XY₁XY₂Z ω).fst.snd.snd
  let Z := fun ω ↦ (XY₁XY₂Z ω).snd
  let X₃ := fun ω ↦ (XY₃ ω).fst
  let Y₃ := fun ω ↦ (XY₃ ω).snd

  -- let XY'vec := ![X', Y', X', Y', X', Y']
  -- have hh := independent_copies' XY'vec ?_
  -- swap; simp only [measurable_discrete, implies_true]

  -- -- this is to unpack `hh`
  -- let νvec := fun (_ : Fin 6) ↦ ν
  -- have (i : Fin 6) : IsProbabilityMeasure (νvec i) := by
  --   unfold_let
  --   dsimp
  --   exact hν
  -- replace hh := @hh νvec this
  -- obtain ⟨Ω₀, mΩ₀, ν₀, XYvec, hν₀, h_indep, h_temp⟩ := hh
  -- rw [forall_and] at h_temp
  -- rcases h_temp with ⟨h_meas, h_ident⟩

  -- let X₁ := XYvec 0
  -- let Y₁ := XYvec 1
  -- let X₂ := XYvec 2
  -- let Y₂ := XYvec 3
  -- let X₃ := XYvec 4
  -- let Y₃ := XYvec 5

  have iX₁Y₃ : IndepFun X₁ Y₃ ν₀ := by
    convert IndepFun.comp h_indep (show Measurable (fun x ↦ x.1.1.1) by measurability)
      (show Measurable (fun x ↦ x.2) by measurability)
  have iX₃Y₂ : IndepFun X₃ Y₂ ν₀ := by
    convert IndepFun.comp h_indep.symm (show Measurable (fun x ↦ x.1) by measurability)
      (show Measurable (fun x ↦ x.1.2.2) by measurability)

  have iX₁Y₁ : IndepFun X₁ Y₁ ν₀ := iIndepFun.indepFun h_indep (show 0 ≠ 1 by simp)

  have iX₂Y₂ : IndepFun X₂ Y₂ ν₀ := iIndepFun.indepFun h_indep (show 2 ≠ 3 by simp)

  -- iIndepFun.indepFun h_indep (show 0 ≠ 5 by simp)

  have iX₃Y₃ : IndepFun X₃ Y₃ ν₀ := iIndepFun.indepFun h_indep (show 4 ≠ 5 by simp)
  have iX₃negY₃ : IndepFun X₃ (-Y₃) ν₀ := iX₃Y₃.comp measurable_id measurable_neg

  -- `PROBLEM 1`
  have i112233 : IndepFun (⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩) (⟨X₃, Y₃⟩) ν₀ := by sorry

  have hX1 : H[X' ; ν] = H[X₁ ; ν₀] := (IdentDistrib.entropy_eq (h_ident 0)).symm
  have hX2 : H[X' ; ν] = H[X₂ ; ν₀] := (IdentDistrib.entropy_eq (h_ident 2)).symm
  have hX3 : H[X' ; ν] = H[X₃ ; ν₀] := (IdentDistrib.entropy_eq (h_ident 4)).symm
  have hY1 : H[Y' ; ν] = H[Y₁ ; ν₀] := (IdentDistrib.entropy_eq (h_ident 1)).symm
  have hY2 : H[Y' ; ν] = H[Y₂ ; ν₀] := (IdentDistrib.entropy_eq (h_ident 3)).symm
  have hY3 : H[Y' ; ν] = H[Y₃ ; ν₀] := (IdentDistrib.entropy_eq (h_ident 5)).symm

  have hnegY3 : H[Y₃ ; ν₀] = H[-Y₃ ; ν₀] := (entropy_neg (h_meas 5)).symm
  have hX1Y1 : H[⟨X₁, Y₁⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX1.symm ▸ hY1.symm ▸ (entropy_pair_eq_add (h_meas 0) (h_meas 1)).mpr iX₁Y₁
  have hX2Y2 : H[⟨X₂, Y₂⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX2.symm ▸ hY2.symm ▸ (entropy_pair_eq_add (h_meas 2) (h_meas 3)).mpr iX₂Y₂
  have hX3Y3 : H[⟨X₃, Y₃⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX3.symm ▸ hY3.symm ▸ (entropy_pair_eq_add (h_meas 4) (h_meas 5)).mpr iX₃Y₃

  have dX3negY3 : d[X' ; ν # -Y' ; ν] = d[X₃ ; ν₀ # -Y₃ ; ν₀] :=
    (IdentDistrib.rdist_eq (h_ident 4) (h_ident 5).neg).symm
  have dX1Y1 : d[X' ; ν # Y' ; ν] = d[X₁ ; ν₀ # Y₁ ; ν₀] :=
    (IdentDistrib.rdist_eq (h_ident 0) (h_ident 1)).symm
  have dX1Y3 : d[X' ; ν # Y' ; ν] = d[X₁ ; ν₀ # Y₃ ; ν₀] :=
    (IdentDistrib.rdist_eq (h_ident 0) (h_ident 5)).symm
  have dX3Y2 : d[X' ; ν # Y' ; ν] = d[X₃ ; ν₀ # Y₂ ; ν₀] :=
    (IdentDistrib.rdist_eq (h_ident 4) (h_ident 3)).symm

  have meas1321 : Measurable (⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩) :=
    ((h_meas 0).sub (h_meas 5)).prod_mk <| (h_meas 2).prod_mk (h_meas 1)
  have meas321321 : Measurable (⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩) :=
    ((h_meas 4).sub (h_meas 3)).prod_mk meas1321
  have meas11 : Measurable (⟨X₁, Y₁⟩) := (h_meas 0).prod_mk (h_meas 1)
  have meas22 : Measurable (⟨X₂, Y₂⟩) := (h_meas 2).prod_mk (h_meas 3)
  have meas1122 : Measurable (⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩) := meas11.prod_mk meas22
  have meas33 : Measurable (⟨X₃, Y₃⟩) := (h_meas 4).prod_mk (h_meas 5)
  have meas1neg1 : Measurable (X₁ - Y₁) := (h_meas 0).sub (h_meas 1)

  have in1 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, ⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩⟩ ; ν₀] + H[X₃ + Y₃; ν₀]
      ≤ H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀] + H[⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩ ; ν₀] :=
    entropy_triple_add_entropy_le _
      (((h_meas 4).sub (h_meas 3)).prod_mk <| ((h_meas 0).sub (h_meas 5)).prod_mk <|
        (h_meas 2).prod_mk (h_meas 1))
      (meas33) ((h_meas 4).add (h_meas 5))
  have eq2 : H[X₃ + Y₃; ν₀] = 1/2 * H[X'; ν] + 1/2 * H[Y'; ν] + d[X'; ν # -Y'; ν] := by
    rw [hX3, hY3, dX3negY3, hnegY3, IndepFun.rdist_eq iX₃negY₃ (h_meas 4) (h_meas 5).neg, sub_neg_eq_add]
    ring
  have eq3 : H[⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩ ; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX3Y3 ▸ entropy_of_comp_eq_of_comp ν₀
      (meas33 |>.prod_mk <| (h_meas 4).add (h_meas 5))
      (meas33) (fun ((x3, y3), xy3) ↦ (x3, y3))
      (fun (x3, y3) ↦ ((x3, y3), x3 + y3)) rfl rfl
   -- `PROBLEM 2`
  have eq4' : X₁ - Y₁ = X₂ - Y₂ := by
    sorry
  have eq4 : X₃ + Y₃ = (X₃ - Y₂) - (X₁ - Y₃) + X₂ + Y₁ := by
    rw [sub_eq_iff_eq_add.mp eq4']
    simp only [sub_eq_add_neg, add_assoc, neg_add_rev, neg_neg, add_left_neg, add_zero,
      neg_add_cancel_comm_assoc]
  have eq5 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀]
      = H[⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩ ; ν₀] :=
      entropy_of_comp_eq_of_comp ν₀ (meas321321.prod_mk <| (h_meas 4).add (h_meas 5)) meas321321
        (fun ((x3y2, (x1y3, (x2, y1))), x3y3) ↦ (x3y2, (x1y3, (x2, y1))))
        (fun (x3y2, (x1y3, (x2, y1))) ↦ ((x3y2, (x1y3, (x2, y1))), x3y2 - x1y3 + x2 + y1))
        rfl (eq4 ▸ rfl)
  have in6 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀]
      ≤ H[X₃ - Y₂; ν₀] + H[X₁ - Y₃; ν₀] + H[X₂; ν₀] + H[Y₁; ν₀] := by
    rw [eq5]
    refine (entropy_pair_le_add ?_ meas1321 ν₀).trans ?_
    · exact ((h_meas 4).sub (h_meas 3))
    simp only [add_assoc, add_le_add_iff_left]
    refine (entropy_pair_le_add ?_ ?_ ν₀).trans ?_
    · exact ((h_meas 0).sub (h_meas 5))
    · exact ((h_meas 2).prod_mk (h_meas 1))
    simp only [add_assoc, add_le_add_iff_left]
    exact entropy_pair_le_add (h_meas 2) (h_meas 1) ν₀
  have eq7 : H[X₃ - Y₂; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX3Y2, IndepFun.rdist_eq iX₃Y₂ (h_meas 4) (h_meas 3), hX3, hY2]
    ring_nf
  have eq8 : H[X₁ - Y₃; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX1Y3, IndepFun.rdist_eq iX₁Y₃ (h_meas 0) (h_meas 5), hX1, hY3]
    ring_nf
  have eq8' : H[X₁ - Y₁; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX1Y1, IndepFun.rdist_eq iX₁Y₁ (h_meas 0) (h_meas 1), hX1, hY1]
    ring_nf
  have in9 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀]
      ≤ 2 * H[X'; ν] + 2 * H[Y'; ν] + 2 * d[X'; ν # Y'; ν] := by
    rw [eq7, eq8, ← hX2, ← hY1] at in6
    ring_nf at in6 ⊢
    exact in6
  have in10 : H[⟨X₁, ⟨Y₁, ⟨X₂, ⟨Y₂, ⟨X₃, Y₃⟩⟩⟩⟩⟩ ; ν₀]
      ≤ H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, ⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩⟩ ; ν₀] := by
    convert entropy_comp_le ν₀
      (meas321321.prod_mk <| (meas33).prod_mk <| (h_meas 4).add (h_meas 5))
      (fun ((x3y2, (x1y3, (x2, y1))), ((x3, y3), x3y3))
        ↦ (x1y3 + y3, (y1, (x2, (x3 - x3y2, (x3, y3))))))
      <;> simp only [comp_apply, Pi.sub_apply, sub_add_cancel, sub_sub_cancel]
  have eq11 : H[⟨X₁, ⟨Y₁, ⟨X₂, ⟨Y₂, ⟨X₃, Y₃⟩⟩⟩⟩⟩ ; ν₀]
      = H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] + H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀]
        - H[X₁ - Y₁; ν₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
    calc
      _ = H[⟨⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩, ⟨X₃, Y₃⟩⟩ ; ν₀] :=
        entropy_of_comp_eq_of_comp ν₀
          ((h_meas 0).prod_mk <| (h_meas 1).prod_mk <| (h_meas 2).prod_mk <|
            (h_meas 3).prod_mk <| meas33)
          (meas1122.prod_mk meas33)
          (fun (x1, (y1, (x2, (y2, (x3, y3))))) ↦ (((x1, y1), (x2, y2)), (x3, y3)))
          (fun (((x1, y1), (x2, y2)), (x3, y3)) ↦ (x1, (y1, (x2, (y2, (x3, y3)))))) rfl rfl
      _ = H[⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩ ; ν₀] + H[⟨X₃, Y₃⟩ ; ν₀] :=
        (entropy_pair_eq_add meas1122 meas33).mpr i112233
      _ = H[⟨⟨X₁, Y₁⟩, ⟨⟨X₂, Y₂⟩, X₁ - Y₁⟩⟩ ; ν₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 1
        exact entropy_of_comp_eq_of_comp ν₀ meas1122
          (meas11.prod_mk <| (meas22).prod_mk <| (h_meas 0).sub (h_meas 1))
          (fun ((x1, y1), (x2, y2)) ↦ ((x1, y1), ((x2, y2), x1 - y1)))
          (fun ((x1, y1), ((x2, y2), x1y1)) ↦ ((x1, y1), (x2, y2))) rfl rfl
      _ = H[⟨⟨X₁, Y₁⟩, X₁ - Y₁⟩ ; ν₀] + H[⟨⟨X₂, Y₂⟩, X₂ - Y₂⟩ ; ν₀] - H[X₁ - Y₁ ; ν₀]
          + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 1
        rw [← eq4']
        refine ent_of_cond_indep (μ := ν₀) meas11 meas22 meas1neg1 ?_
        sorry -- `PROBLEM 3`
      _ = H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] + H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀]
          - H[X₁ - Y₁; ν₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 3
        · exact entropy_of_comp_eq_of_comp ν₀ (meas11.prod_mk meas1neg1)
            ((h_meas 0).prod_mk <| (h_meas 1).prod_mk <| (h_meas 0).sub (h_meas 1))
            (fun ((x1, y1),x1y1) ↦ (x1, (y1, x1y1))) (fun (x1, (y1, x1y1)) ↦ ((x1, y1),x1y1))
            rfl rfl
        · exact entropy_of_comp_eq_of_comp ν₀ (meas22.prod_mk <| (h_meas 2).sub (h_meas 3))
            ((h_meas 2).prod_mk <| (h_meas 3).prod_mk <| (h_meas 2).sub (h_meas 3))
            (fun ((x1, y1),x1y1) ↦ (x1, (y1, x1y1))) (fun (x1, (y1, x1y1)) ↦ ((x1, y1),x1y1))
            rfl rfl
  have eq12_aux1 : H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] = H[⟨X₁, Y₁⟩ ; ν₀] :=
    entropy_of_comp_eq_of_comp ν₀
      ((h_meas 0).prod_mk <| (h_meas 1).prod_mk <| (h_meas 0).sub (h_meas 1)) meas11
      (fun (x1, (y1, x1y1)) ↦ (x1, y1)) (fun (x1, y1) ↦ (x1, (y1, x1 - y1))) rfl rfl
  have eq12_aux2 : H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀] = H[⟨X₂, Y₂⟩ ; ν₀] :=
    entropy_of_comp_eq_of_comp ν₀
      ((h_meas 2).prod_mk <| (h_meas 3).prod_mk <| (h_meas 2).sub (h_meas 3)) meas22
      (fun (x1, (y1, x1y1)) ↦ (x1, y1)) (fun (x1, y1) ↦ (x1, (y1, x1 - y1))) rfl rfl
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
    _ = 2 * (H[X' ; ν] + H[Y' ; ν]) + 2 * d[X' ; ν # Y' ; ν] + H[X' ; ν] + H[Y' ; ν] := by
      simp only [eq3]
      ring
    _ = 3 * (H[X' ; ν] + H[Y' ; ν]) + 2 * d[X' ; ν # Y' ; ν] := by
      ring

--open Classical in
/--  If $n \geq 1$ and $X, Y_1, \dots, Y_n$ are jointly independent $G$-valued random variables, then
  $$ H[X + \sum_{i=1}^n Y_i] - H[X] \leq \sum_{i=1}^n H[X+Y_i] - \bbH[X].$$
The spelling here is tentative.  Feel free to modify it to make the proof easier, or the application easier. -/
lemma kvm_ineq_I {I:Type*} {i₀: I} {s: Finset I} (hs: ¬ i₀ ∈ s) (Y: I → Ω → G) (hY: (i:I) → Measurable (Y i))
                 (hindep: iIndepFun (fun (i:I) => hG) Y μ )
                : H[ Y i₀ + ∑ i in s, Y i; μ ] - H[ Y i₀; μ ] ≤ ∑ i in s, (H[ Y i₀ + Y i; μ] - H[Y i₀; μ]) := by sorry

/--  If $n \geq 1$ and $X, Y_1, \dots, Y_n$ are jointly independent $G$-valued random variables, then
  $$ d[X; \sum_{i=1}^n Y_i] \leq 2 \sum_{i=1}^n d[X; Y_i].$$
-/
lemma kvm_ineq_II {I:Type*} {i₀: I} {s: Finset I} (hs: ¬ i₀ ∈ s) (hs': Finset.Nonempty s) (Y: I → Ω → G)
                 (hY: (i:I) → Measurable (Y i)) (hindep: iIndepFun (fun (i:I) => hG) Y μ )
                : d[Y i₀; μ # ∑ i in s, Y i; μ ] ≤ 2 * ∑ i in s, d[Y i₀; μ # Y i; μ] := by sorry

/-- If $n \geq 1$ and $X, Y_1, \dots, Y_n$ are jointly independent $G$-valued random variables, then
  $$ d[X; \sum_{i=1}^n Y_i] \leq d[X; Y_1] + \frac{1}{2}(\bbH[ \sum_{i=1}^n Y_i ] - \bbH[Y_1]).$$
-/
lemma kvm_ineq_III {I:Type*} {i₀ : I} {s: Finset I} (hs: ¬ i₀ ∈ s) (hs': Finset.Nonempty s) (Y: I → Ω → G)
                 (hY: (i:I) → Measurable (Y i)) (hindep: iIndepFun (fun (i:I) => hG) Y μ ) (i₁ : I)
                : d[Y i₀; μ # ∑ i in s, Y i; μ ] ≤ d[Y i₀; μ # Y i₁; μ] + (2:ℝ)⁻¹ * ∑ i in s, (H[Y i; μ] - H[Y i₁; μ]) := by sorry

/-- Let $(X_i)_{1 \leq i \leq m}$ and $(Y_j)_{1 \leq j \leq l}$ be tuples of jointly independent random variables (so the $X$'s and $Y$'s are also independent of each other), and let $f: \{1,\dots,l\} \to \{1,\dots,m\}$ be a function, then
  $$ \bbH[\sum_{j=1}^l Y_j] \leq \bbH[ \sum_{i=1}^m X_i ] + \sum_{j=1}^l (\bbH[ Y_j - X_{f(j)}] - \bbH[X_{f(j)}]).$$
-/
lemma ent_of_sum_le_ent_of_sum : 0 = 1 := by sorry

/-- Let `X,Y,X'` be independent `G`-valued random variables, with `X'` a copy of `X`, and
let `a` be an integer.  Then `H[X - (a+1)Y] ≤ H[X - aY] + H[X - Y - X'] - H[X]` -/
lemma ent_of_sub_smul {Y : Ω → G} {X' : Ω → G} [FiniteRange Y] [FiniteRange X'] (hX: Measurable X) (hY: Measurable Y) (hX': Measurable X') (hindep: iIndepFun (fun _ ↦ hG) ![X, Y, X'] μ) (hident: IdentDistrib X X' μ μ) {a:ℤ} : H[X - (a+1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] := by sorry

/-- Let `X,Y,X'` be independent `G`-valued random variables, with `X'` a copy of `X`,
and let `a` be an integer.  Then `H[X - (a-1)Y] ≤ H[X - aY] + H[X - Y - X'] - H[X]`. -/
lemma ent_of_sub_smul' {Y : Ω → G} {X' : Ω → G} [FiniteRange Y] [FiniteRange X'] (hX: Measurable X) (hY: Measurable Y) (hX': Measurable X') (hindep: iIndepFun (fun _ ↦ hG) ![X, Y, X'] μ) (hident: IdentDistrib X X' μ μ) {a:ℤ} : H[X - (a-1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] := by sorry

/--  Let `X,Y` be independent `G`-valued random variables, and let `a` be an integer.  Then
  `H[X - aY] - H[X] ≤ 4 |a| d[X ; Y]`. -/
lemma ent_of_sub_smul_le {Y : Ω → G} [FiniteRange Y] (hX: Measurable X) (hY: Measurable Y) (hindep: IndepFun X Y μ) {a:ℤ} : H[X - a • Y; μ] - H[X; μ] ≤ 4 * |a| * d[X ; μ # Y ; μ] := by sorry

section multiDistance

open Filter Function MeasureTheory Measure ProbabilityTheory
open scoped BigOperators

variable {G : Type*}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G]
  [MeasurableSub₂ G] [MeasurableAdd₂ G] [Countable G]

/--  Let $X_{[m]} = (X_i)_{1 \leq i \leq m}$ non-empty finite tuple of $G$-valued random variables $X_i$. Then we define
\[
  D[X_{[m]}] := \bbH[\sum_{i=1}^m \tilde X_i] - \frac{1}{m} \sum_{i=1}^m \bbH[\tilde X_i],
\]
where the $\tilde X_i$ are independent copies of the $X_i$.-/
noncomputable
def multiDist {m:ℕ} {Ω: Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (X : (i:Fin m) → (Ω i) → G) : ℝ := sorry

@[inherit_doc multiDist] notation3:max "D[" X " ; " hΩ "]" => multiDist hΩ X

/-- For any such tuple, we have $D[X_{[m]}] \geq 0$. -/
lemma multiDist_nonneg : 0 = 1 := by sorry

/--  If $\phi: \{1,\dots,m\} \to \{1,\dots,m\}$ is a bijection, then $D[X_{[m]}] = D[(X_{\phi(j)})_{1 \leq j \leq m}]$. -/
lemma multiDist_of_perm : 0 = 1 := by sorry

/-- Let $m \ge 2$, and let $X_{[m]}$ be a tuple of $G$-valued random variables. Then
  $$\sum_{1 \leq j,k \leq m: j \neq k} d[X_j; -X_k] \leq m(m-1) D[X_{[m]}].$$ -/
lemma multidist_ruzsa_I : 0 = 1 := by sorry

/-- Let $m \ge 2$, and let $X_{[m]}$ be a tuple of $G$-valued random variables. Then
  $$\sum_{j=1}^m d[X_j;X_j] \leq 2 m D[X_{[m]}].$$ -/
lemma multidist_ruzsa_II : 0 = 1 := by sorry

/-- Let $I$ be an indexing set of size $m \ge 2$, and let $X_{[m]}$ be a tuple of $G$-valued random variables. If the $X_i$ all have the same distribution, then $D[X_{[m]}] \leq m d[X_i;X_i]$ for any $1 \leq i \leq m$. -/
lemma multidist_ruzsa_III : 0 = 1 := by sorry

/-- Let $I$ be an indexing set of size $m \ge 2$, and let $X_{[m]}$ be a tuple of $G$-valued random variables.  Let $W := \sum_{i \in I} X_i$. Then
  $$ d[W;-W] \leq 2 D[X_i].$$ -/
lemma multidist_ruzsa_IV : 0 = 1 := by sorry

/-- If $D[X_{[m]}]=0$, then for each $i \in I$ there is a finite subgroup $H_i \leq G$ such that $d[X_i; U_{H_i}] = 0$. -/
lemma multidist_eq_zero : 0 = 1 := by sorry

/-- If $X_{[m]} = (X_i)_{1 \leq i \leq m}$ and $Y_{[m]} = (Y_i)_{1 \leq i \leq m}$ are tuples of random variables, with the $X_i$ being $G$-valued (but the $Y_i$ need not be), then we define
  \begin{equation}\label{multi-def-cond}
  D[ X_{[m]} | Y_{[m]}] := \bbH[\sum_{i=1}^m \tilde X_i \big| (\tilde Y_j)_{1 \leq j \leq m} ] - \frac{1}{m} \sum_{i=1}^m \bbH[ \tilde X_i | \tilde Y_i]
    \end{equation}
  where $(\tilde X_i,\tilde Y_i)$, $1 \leq i \leq m$ are independent copies of $(X_i,Y_i), 1 \leq i \leq m$ (but note here that we do \emph{not} assume $X_i$ are independent of $Y_i$, or $\tilde X_i$ independent of $\tilde Y_i$). -/
noncomputable
def condMultiDist {m:ℕ} {Ω: Fin m → Type*} (hΩ: (i:Fin m) → MeasureSpace (Ω i)) (X : (i:Fin m) → (Ω i) → G) (Y : (i:Fin m) → (Ω i) → G) : ℝ := sorry

@[inherit_doc multiDist] notation3:max "D[" X " | " Y " ; " hΩ "]" => condMultiDist hΩ X Y

/-- With the above notation, we have
  \begin{equation}\label{multi-def-cond-alt}
    D[ X_{[m]} | Y_{[m]} ] = \sum_{(y_i)_{1 \leq i \leq m}} \biggl(\prod_{1 \leq i \leq m} p_{Y_i}(y_i)\biggr) D[ (X_i \,|\, Y_i \mathop{=}y_i)_{1 \leq i \leq m}]
  \end{equation}
  where each $y_i$ ranges over the support of $p_{Y_i}$ for $1 \leq i \leq m$. -/
lemma condMultiDist_eq : 0 = 1 := by sorry

end multiDistance
