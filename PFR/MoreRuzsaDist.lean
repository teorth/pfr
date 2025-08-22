import PFR.ForMathlib.Entropy.RuzsaDist
import PFR.HundredPercent
import PFR.Mathlib.Algebra.BigOperators.Fin
import PFR.Mathlib.Data.Fin.Basic
import PFR.Mathlib.MeasureTheory.Group.Arithmetic
import PFR.Mathlib.Order.Interval.Finset.Fin

/-!
# More results about Ruzsa distance

More facts about Ruzsa distance and related inequalities, for use in the m-torsion version of PFR.

## Main definitions

* `multiDist`: An analogue of `rdist` for the m-torsion version of PFR.
* `condMultiDist`: A conditional analogue of `multiDist`

## Main results

* `kvm_ineq_I`, `kvm_ineq_II`, `kvm_ineq_III`: Variants of the Kaimanovich-Versik-Madiman inequality
* `multiDist_chainRule`: A chain rule for `multiDist`
* `cor_multiDist_chainRule`: The corollary of the chain rule needed for the m-torsion version of PFR
* `ent_sub_zsmul_sub_ent_le`: Controlling `H[X - aY]` in terms of `H[X]` and `d[X ; Y]`.
-/

open Filter Function MeasureTheory Measure ProbabilityTheory

universe uG

variable {Ω Ω' Ω'' Ω''' S T : Type*} {G: Type uG}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G] [Countable G]
  [Countable S] [MeasurableSpace S]
  [Countable T] [MeasurableSpace T]

variable {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G} -- [FiniteRange X] [FiniteRange Y] [FiniteRange Z]

/-`TODO`: we had to add the hp `Fintype G` to the following lemma in order to use `condIndep_copies`,
which requires it. Actually, we already have `FiniteRange X` and `FiniteRange Y`, so it should be
possible to remove it, or to generalize the lemma to the case where `G` is not finite but the
random variables have finite range. One way to do it may be to write a lemma that tells us that
given a r.v., we can construct another r.v. that is identically distributed, which is defined the
immersion of the range of the initial r.v. inside the codomain (this would be a sort of canonical
version)-/

/-- If `X, Y` are `G`-valued, then `d[X;-Y] ≤ 3 d[X;Y]`. -/
lemma rdist_of_neg_le [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hX : Measurable X)
    (hY : Measurable Y) [Fintype G] :
    d[X ; μ # -Y ; μ'] ≤ 3 * d[X ; μ # Y ; μ'] := by
  obtain ⟨ν, X', Y', hν, mX', mY', h_indep', hXX', hYY'⟩ := independent_copies hX hY μ μ'
  rw [← hXX'.rdist_congr hYY', ← hXX'.rdist_congr hYY'.neg]
  obtain ⟨Ω₀, mΩ₀, XY'₁, XY'₂, Z', ν'₀, hν'₀, hXY'₁, hXY'₂, hZ', h_condIndep, h_id1sub, h_id2sub⟩
    := condIndep_copies (⟨X', Y'⟩) (X' - Y') (mX'.prodMk mY') (by fun_prop) ν
  let X₁' := fun ω ↦ (XY'₁ ω).fst
  let Y'₁ := fun ω ↦ (XY'₁ ω).snd
  let X₂' := fun ω ↦ (XY'₂ ω).fst
  let Y'₂ := fun ω ↦ (XY'₂ ω).snd
  have mX₁' : Measurable X₁' := by fun_prop
  have mY'₁ : Measurable Y'₁ := by fun_prop
  have Z'eq1 : Z' =ᵐ[ν'₀] X₁' - Y'₁ :=
    (IdentDistrib.ae_snd h_id1sub.symm (MeasurableSet.of_discrete (s := {x | x.2 = x.1.1 - x.1.2}))
      (Eventually.of_forall fun ω ↦ rfl) :)
  obtain ⟨ν₀, XY₁XY₂Z, XY₃, hν₀, hXY₁XY₂Z, hXY₃, h_indep, h_idXY₁XY₂Z, h_idXY₃⟩ :=
    independent_copies (hXY'₁.prodMk hXY'₂ |>.prodMk hZ') (mX'.prodMk mY') ν'₀ ν
  let X₁ ω := (XY₁XY₂Z ω).fst.fst.fst
  let Y₁ ω := (XY₁XY₂Z ω).fst.fst.snd
  let X₂ ω := (XY₁XY₂Z ω).fst.snd.fst
  let Y₂ ω := (XY₁XY₂Z ω).fst.snd.snd
  let Z ω := (XY₁XY₂Z ω).snd
  let X₃ ω := (XY₃ ω).fst
  let Y₃ ω := (XY₃ ω).snd
  have mX₁ : Measurable X₁ := by fun_prop
  have mY₁ : Measurable Y₁ := by fun_prop
  have mX₂ : Measurable X₂ := by fun_prop
  have mY₂ : Measurable Y₂ := by fun_prop
  have mX₃ : Measurable X₃ := by fun_prop
  have mY₃ : Measurable Y₃ := by fun_prop
  have mZ : Measurable Z := by fun_prop
  have idXY₁Z : IdentDistrib (⟨⟨X₁, Y₁⟩, Z⟩) (⟨⟨X', Y'⟩, X' - Y'⟩) ν₀ ν :=
    h_idXY₁XY₂Z.comp (.of_discrete (f := fun x ↦ (x.1.1, x.2))) |>.trans h_id1sub
  have idXY₂Z : IdentDistrib (⟨⟨X₂, Y₂⟩, Z⟩) (⟨⟨X', Y'⟩, X' - Y'⟩) ν₀ ν :=
    h_idXY₁XY₂Z.comp (.of_discrete (f := fun x ↦ (x.1.2, x.2))) |>.trans h_id2sub
  have idXY₁ : IdentDistrib (⟨X₁, Y₁⟩) (⟨X', Y'⟩) ν₀ ν := by
    convert h_idXY₁XY₂Z.comp (.of_discrete (f := fun x ↦ x.1.1)) |>.trans ?_
    exact h_id1sub.comp (.of_discrete (f := fun ((x, y), _) ↦ (x, y)))
  have idXY₂ : IdentDistrib (⟨X₂, Y₂⟩) (⟨X', Y'⟩) ν₀ ν := by
    convert h_idXY₁XY₂Z.comp (.of_discrete (f := fun x ↦ x.1.2)) |>.trans ?_
    exact h_id2sub.comp (.of_discrete (f := fun ((x, y), _) ↦ (x, y)))
  have idXY₃ : IdentDistrib (⟨X₃, Y₃⟩) (⟨X', Y'⟩) ν₀ ν := h_idXY₃
  have idX₁ : IdentDistrib X₁ X' ν₀ ν := idXY₁.comp (by fun_prop)
  have idY₁ : IdentDistrib Y₁ Y' ν₀ ν := idXY₁.comp (by fun_prop)
  have idX₂ : IdentDistrib X₂ X' ν₀ ν := idXY₂.comp (by fun_prop)
  have idY₂ : IdentDistrib Y₂ Y' ν₀ ν := idXY₂.comp (by fun_prop)
  have idX₃ : IdentDistrib X₃ X' ν₀ ν := idXY₃.comp (by fun_prop)
  have idY₃ : IdentDistrib Y₃ Y' ν₀ ν := idXY₃.comp (by fun_prop)
  have idXY₁₂XY'₁₂ : IdentDistrib (⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩) (⟨⟨X₁', Y'₁⟩, ⟨X₂', Y'₂⟩⟩) ν₀ ν'₀ :=
    h_idXY₁XY₂Z.comp (.of_discrete (f := fun x ↦ x.1))
  have idXY₁ZXY'₁Z' : IdentDistrib (⟨⟨X₁, Y₁⟩, Z⟩) (⟨⟨X₁', Y'₁⟩, Z'⟩) ν₀ ν'₀ :=
    h_idXY₁XY₂Z.comp (.of_discrete (f := fun x ↦ (x.1.1, x.2)))
  have idXY₂ZXY'₂Z' : IdentDistrib (⟨⟨X₂, Y₂⟩, Z⟩) (⟨⟨X₂', Y'₂⟩, Z'⟩) ν₀ ν'₀ :=
    h_idXY₁XY₂Z.comp (.of_discrete (f := fun x ↦ (x.1.2, x.2)))
  have idZZ' : IdentDistrib Z Z' ν₀ ν'₀ :=
    h_idXY₁XY₂Z.comp .of_discrete
  have Zeq1 : Z =ᵐ[ν₀] X₁ - Y₁ := (IdentDistrib.ae_snd idXY₁Z.symm
      (MeasurableSet.of_discrete (s := {x | x.2 = x.1.1 - x.1.2}))
      (Eventually.of_forall fun ω ↦ rfl) :)
  have Zeq2 : Z =ᵐ[ν₀] X₂ - Y₂ :=
    (IdentDistrib.ae_snd idXY₂Z.symm (MeasurableSet.of_discrete (s := {x | x.2 = x.1.1 - x.1.2}))
      (Eventually.of_forall fun ω ↦ rfl) :)
  have iX₁Y₃ : IndepFun X₁ Y₃ ν₀ := by
    convert h_indep.comp (.of_discrete (f := fun x ↦ x.1.1.1)) (.of_discrete (f := fun x ↦ x.2))
  have iX₃Y₂ : IndepFun X₃ Y₂ ν₀ := by
    convert h_indep.symm.comp (.of_discrete (f := fun x ↦ x.1)) (.of_discrete (f := fun x ↦ x.1.2.2))
  have iX₁Y₁ : IndepFun X₁ Y₁ ν₀ := indepFun_of_identDistrib_pair h_indep' idXY₁.symm
  have iX₂Y₂ : IndepFun X₂ Y₂ ν₀ := indepFun_of_identDistrib_pair h_indep' idXY₂.symm
  have iX₃Y₃ : IndepFun X₃ Y₃ ν₀ := indepFun_of_identDistrib_pair h_indep' idXY₃.symm
  have iX₃negY₃ : IndepFun X₃ (-Y₃) ν₀ := iX₃Y₃.comp measurable_id measurable_neg
  have i112233 : IndepFun (⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩) (⟨X₃, Y₃⟩) ν₀ :=
    h_indep.comp (.of_discrete (f := fun (xy, _) ↦ xy)) measurable_id
  have hX1 : H[X' ; ν] = H[X₁ ; ν₀] := idX₁.entropy_congr.symm
  have hX2 : H[X' ; ν] = H[X₂ ; ν₀] := idX₂.entropy_congr.symm
  have hX3 : H[X' ; ν] = H[X₃ ; ν₀] := idX₃.entropy_congr.symm
  have hY1 : H[Y' ; ν] = H[Y₁ ; ν₀] := idY₁.entropy_congr.symm
  have hY2 : H[Y' ; ν] = H[Y₂ ; ν₀] := idY₂.entropy_congr.symm
  have hY3 : H[Y' ; ν] = H[Y₃ ; ν₀] := idY₃.entropy_congr.symm
  have hnegY3 : H[Y₃ ; ν₀] = H[-Y₃ ; ν₀] := (entropy_neg mY₃).symm
  have hX1Y1 : H[⟨X₁, Y₁⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX1.symm ▸ hY1.symm ▸ (entropy_pair_eq_add mX₁ mY₁).mpr iX₁Y₁
  have hX2Y2 : H[⟨X₂, Y₂⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX2.symm ▸ hY2.symm ▸ (entropy_pair_eq_add mX₂ mY₂).mpr iX₂Y₂
  have hX3Y3 : H[⟨X₃, Y₃⟩; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX3.symm ▸ hY3.symm ▸ (entropy_pair_eq_add mX₃ mY₃).mpr iX₃Y₃
  have dX3negY3 : d[X' ; ν # -Y' ; ν] = d[X₃ ; ν₀ # -Y₃ ; ν₀] := (idX₃.rdist_congr idY₃.neg).symm
  have dX1Y1 : d[X' ; ν # Y' ; ν] = d[X₁ ; ν₀ # Y₁ ; ν₀] := (idX₁.rdist_congr idY₁).symm
  have dX1Y3 : d[X' ; ν # Y' ; ν] = d[X₁ ; ν₀ # Y₃ ; ν₀] := (idX₁.rdist_congr idY₃).symm
  have dX3Y2 : d[X' ; ν # Y' ; ν] = d[X₃ ; ν₀ # Y₂ ; ν₀] := (idX₃.rdist_congr idY₂).symm
  have meas1321 : Measurable (⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩) := (mX₁.sub mY₃).prodMk <| mX₂.prodMk mY₁
  have meas321321 : Measurable (⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩) := (mX₃.sub mY₂).prodMk meas1321
  have meas11 : Measurable (⟨X₁, Y₁⟩) := mX₁.prodMk mY₁
  have meas22 : Measurable (⟨X₂, Y₂⟩) := mX₂.prodMk mY₂
  have meas1122 : Measurable (⟨⟨X₁, Y₁⟩, ⟨X₂, Y₂⟩⟩) := meas11.prodMk meas22
  have meas33 : Measurable (⟨X₃, Y₃⟩) := mX₃.prodMk mY₃
  have meas1neg1 : Measurable (X₁ - Y₁) := mX₁.sub mY₁
  have in1 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, ⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩⟩ ; ν₀] + H[X₃ + Y₃; ν₀]
      ≤ H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀] + H[⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩ ; ν₀] :=
    entropy_triple_add_entropy_le _ (by fun_prop) meas33 (mX₃.add mY₃)
  have eq2 : H[X₃ + Y₃; ν₀] = 1/2 * H[X'; ν] + 1/2 * H[Y'; ν] + d[X'; ν # -Y'; ν] := by
    rw [hX3, hY3, dX3negY3, hnegY3, iX₃negY₃.rdist_eq mX₃ mY₃.neg, sub_neg_eq_add]
    ring
  have eq3 : H[⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩ ; ν₀] = H[X'; ν] + H[Y'; ν] :=
    hX3Y3 ▸ entropy_of_comp_eq_of_comp ν₀ (meas33 |>.prodMk <| mX₃.add mY₃) meas33
      (fun ((x3, y3), _) ↦ (x3, y3)) (fun (x3, y3) ↦ ((x3, y3), x3 + y3)) rfl rfl
  have eq4' : X₁ =ᵐ[ν₀] X₂ - Y₂ + Y₁ := by
    filter_upwards [Zeq1, Zeq2] with ω hZ hZ'
    simp only [Pi.add_apply, ← hZ', hZ, Pi.sub_apply, sub_add_cancel]
  have eq4 : X₃ + Y₃ =ᵐ[ν₀] (X₃ - Y₂) - (X₁ - Y₃) + X₂ + Y₁ := by
    filter_upwards [eq4'] with ω h
    simp only [Pi.add_apply, sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, Pi.neg_apply, h,
      neg_add_cancel, add_zero, neg_add_cancel_comm_assoc]
  have eq5 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀]
      = H[⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩ ; ν₀] :=
    calc
      _ = H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, (X₃ - Y₂) - (X₁ - Y₃) + X₂ + Y₁⟩ ; ν₀] := by
        refine IdentDistrib.entropy_congr <|
          IdentDistrib.of_ae_eq (meas321321.prodMk <| mX₃.add mY₃).aemeasurable ?_
        filter_upwards [eq4] with ω h
        simp only [Prod.mk.injEq, h, Pi.add_apply, Pi.sub_apply, and_self]
      _ = _ := by
        refine entropy_of_comp_eq_of_comp ν₀
          (meas321321.prodMk <| (((mX₃.sub mY₂).sub (mX₁.sub mY₃)).add mX₂).add mY₁) meas321321
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
    · exact (mX₂.prodMk mY₁)
    simp only [add_le_add_iff_left]
    exact entropy_pair_le_add mX₂ mY₁ ν₀
  have eq7 : H[X₃ - Y₂; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX3Y2, iX₃Y₂.rdist_eq mX₃ mY₂, hX3, hY2]
    ring_nf
  have eq8 : H[X₁ - Y₃; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX1Y3, iX₁Y₃.rdist_eq mX₁ mY₃, hX1, hY3]
    ring_nf
  have eq8' : H[X₁ - Y₁; ν₀] = 1/2 * (H[X'; ν] + H[Y'; ν]) + d[X'; ν # Y'; ν] := by
    rw [dX1Y1, iX₁Y₁.rdist_eq mX₁ mY₁, hX1, hY1]
    ring_nf
  have in9 : H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, X₃ + Y₃⟩ ; ν₀]
      ≤ 2 * H[X'; ν] + 2 * H[Y'; ν] + 2 * d[X'; ν # Y'; ν] := by
    rw [eq7, eq8, ← hX2, ← hY1] at in6
    ring_nf at in6 ⊢
    exact in6
  have in10 : H[⟨X₁, ⟨Y₁, ⟨X₂, ⟨Y₂, ⟨X₃, Y₃⟩⟩⟩⟩⟩ ; ν₀]
      ≤ H[⟨⟨X₃ - Y₂, ⟨X₁ - Y₃, ⟨X₂, Y₁⟩⟩⟩, ⟨⟨X₃, Y₃⟩, X₃ + Y₃⟩⟩ ; ν₀] := by
    convert entropy_comp_le ν₀
      (meas321321.prodMk <| meas33.prodMk <| mX₃.add mY₃)
      (fun ((x3y2, x1y3, x2, y1), (x3, y3), _) ↦ (x1y3 + y3, y1, x2, x3 - x3y2, x3, y3))
      <;> simp only [comp_apply, Pi.sub_apply, sub_add_cancel, sub_sub_cancel]
  have eq11 : H[⟨X₁, ⟨Y₁, ⟨X₂, ⟨Y₂, ⟨X₃, Y₃⟩⟩⟩⟩⟩ ; ν₀]
      = H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] + H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀]
        - H[X₁ - Y₁; ν₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
    calc
      _ = H[⟨⟨X₁', Y'₁⟩, ⟨X₂', Y'₂⟩⟩ ; ν'₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        rw [← idXY₁₂XY'₁₂.entropy_congr, ← (entropy_pair_eq_add meas1122 meas33).mpr i112233]
        exact entropy_of_comp_eq_of_comp ν₀
          (mX₁.prodMk <| mY₁.prodMk <| mX₂.prodMk <| mY₂.prodMk <| meas33)
          (meas1122.prodMk meas33)
          (fun (x1, (y1, (x2, (y2, (x3, y3))))) ↦ (((x1, y1), (x2, y2)), (x3, y3)))
          (fun (((x1, y1), (x2, y2)), (x3, y3)) ↦ (x1, (y1, (x2, (y2, (x3, y3)))))) rfl rfl
      _ = H[⟨⟨X₁', Y'₁⟩, ⟨⟨X₂', Y'₂⟩, X₁' - Y'₁⟩⟩ ; ν'₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 1
        exact entropy_of_comp_eq_of_comp ν'₀ (hXY'₁.prodMk hXY'₂)
          (hXY'₁.prodMk <| hXY'₂.prodMk <| mX₁'.sub mY'₁)
          (fun ((x1, y1), (x2, y2)) ↦ ((x1, y1), ((x2, y2), x1 - y1)))
          (fun ((x1, y1), ((x2, y2), _)) ↦ ((x1, y1), (x2, y2))) rfl rfl
      _ = H[⟨⟨X₁', Y'₁⟩, ⟨⟨X₂', Y'₂⟩, Z'⟩⟩ ; ν'₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 1
        refine IdentDistrib.entropy_congr <| IdentDistrib.of_ae_eq
          (hXY'₁.prodMk <| hXY'₂.prodMk <| mX₁'.sub mY'₁).aemeasurable ?_
        filter_upwards [Z'eq1] with ω h
        simp only [Prod.mk.injEq, Pi.sub_apply, h, and_self]
      _ = H[⟨⟨X₁, Y₁⟩, Z⟩ ; ν₀] + H[⟨⟨X₂, Y₂⟩, Z⟩ ; ν₀] - H[Z ; ν₀]
          + H[⟨X₃, Y₃⟩ ; ν₀] := by
        rw [ent_of_cond_indep (μ := ν'₀) hXY'₁ hXY'₂ hZ' h_condIndep, idXY₁ZXY'₁Z'.entropy_congr,
          idXY₂ZXY'₂Z'.entropy_congr, idZZ'.entropy_congr]
      _ = H[⟨⟨X₁, Y₁⟩, X₁ - Y₁⟩ ; ν₀] + H[⟨⟨X₂, Y₂⟩, X₂ - Y₂⟩ ; ν₀] - H[X₁ - Y₁ ; ν₀]
          + H[⟨X₃, Y₃⟩ ; ν₀] := by
        rw [IdentDistrib.entropy_congr <| IdentDistrib.of_ae_eq mZ.aemeasurable Zeq1]
        congr 3
        · refine IdentDistrib.entropy_congr <| IdentDistrib.of_ae_eq
            (((mX₁.prodMk mY₁).prodMk mZ).aemeasurable) ?_
          filter_upwards [Zeq1] with ω h
          simp only [Prod.mk.injEq, h, Pi.sub_apply, and_self]
        · refine IdentDistrib.entropy_congr <| IdentDistrib.of_ae_eq
            ((mX₂.prodMk mY₂).prodMk mZ).aemeasurable ?_
          filter_upwards [Zeq2] with ω h
          simp only [Prod.mk.injEq, h, Pi.sub_apply, and_self]
      _ = H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] + H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀]
          - H[X₁ - Y₁; ν₀] + H[⟨X₃, Y₃⟩ ; ν₀] := by
        congr 3
        · exact entropy_of_comp_eq_of_comp ν₀ (meas11.prodMk meas1neg1)
            (mX₁.prodMk <| mY₁.prodMk <| mX₁.sub mY₁)
            (fun ((x1, y1),x1y1) ↦ (x1, (y1, x1y1))) (fun (x1, (y1, x1y1)) ↦ ((x1, y1),x1y1))
            rfl rfl
        · exact entropy_of_comp_eq_of_comp ν₀ (meas22.prodMk <| (mX₂).sub (mY₂))
            (mX₂.prodMk <| mY₂.prodMk <| mX₂.sub mY₂)
            (fun ((x1, y1),x1y1) ↦ (x1, (y1, x1y1))) (fun (x1, (y1, x1y1)) ↦ ((x1, y1),x1y1))
            rfl rfl
  have eq12_aux1 : H[⟨X₁, ⟨Y₁, X₁ - Y₁⟩⟩ ; ν₀] = H[⟨X₁, Y₁⟩ ; ν₀] :=
    entropy_of_comp_eq_of_comp ν₀
      (mX₁.prodMk <| mY₁.prodMk <| mX₁.sub mY₁) meas11
      (fun (x1, (y1, _)) ↦ (x1, y1)) (fun (x1, y1) ↦ (x1, (y1, x1 - y1))) rfl rfl
  have eq12_aux2 : H[⟨X₂, ⟨Y₂, X₂ - Y₂⟩⟩ ; ν₀] = H[⟨X₂, Y₂⟩ ; ν₀] :=
    entropy_of_comp_eq_of_comp ν₀
      (mX₂.prodMk <| mY₂.prodMk <| mX₂.sub mY₂) meas22
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

/-- If `n ≥ 0` and `X, Y₁, ..., Yₙ` are jointly independent `G`-valued random variables,
then `H[Y i₀ + ∑ i ∈ s, Y i; μ] - H[Y i₀; μ] ≤ ∑ i ∈ s, (H[Y i₀ + Y i; μ] - H[Y i₀; μ])`.
 -/
lemma kvm_ineq_I {I : Type*} {i₀ : I} {s : Finset I} (hs : ¬ i₀ ∈ s)
    {Y : I → Ω → G} [∀ i, FiniteRange (Y i)] (hY : ∀ i, Measurable (Y i))
    (h_indep : iIndepFun Y μ) :
    H[Y i₀ + ∑ i ∈ s, Y i ; μ] - H[Y i₀ ; μ] ≤ ∑ i ∈ s, (H[Y i₀ + Y i ; μ] - H[Y i₀ ; μ]) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi IH =>
    simp_rw [Finset.sum_insert hi]
    have his : i₀ ∉ s := fun h ↦ hs (Finset.mem_insert_of_mem h)
    have hii₀ : i ≠ i₀ := fun h ↦ hs (h ▸ Finset.mem_insert_self i s)
    let J := Fin 3
    let S : J → Finset I := ![s, {i₀}, {i}]
    have h_dis : Set.univ.PairwiseDisjoint S := by
      intro j _ k _ hjk
      change Disjoint (S j) (S k)
      fin_cases j <;> fin_cases k <;> try exact (hjk rfl).elim
      all_goals
        simp_all [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
          Finset.disjoint_singleton_right, S]
    let φ : (j : J) → ((_ : S j) → G) → G
      | 0 => fun Ys ↦ ∑ i : s, Ys ⟨i.1, i.2⟩
      | 1 => fun Ys ↦ Ys ⟨i₀, by simp [S]⟩
      | 2 => fun Ys ↦ Ys ⟨i, by simp [S]⟩
    have hφ : (j : J) → Measurable (φ j) := fun j ↦ .of_discrete
    have h_ind : iIndepFun ![∑ j ∈ s, Y j, Y i₀, Y i] μ := by
      convert h_indep.finsets_comp S h_dis hY φ hφ with j x
      fin_cases j <;> simp [φ, (s.sum_attach _).symm]
    have measSum : Measurable (∑ j ∈ s, Y j) := by
      convert Finset.measurable_sum s (fun j _ ↦ hY j)
      simp
    have hkv := kaimanovich_vershik h_ind measSum (hY i₀) (hY i)
    convert add_le_add (IH his) hkv using 1
    · nth_rw 2 [add_comm (Y i₀)]
      norm_num
      congr 1
      rw [add_comm _ (Y i₀), add_comm (Y i), add_assoc]
    · ring

/-- If `n ≥ 1` and `X, Y₁, ..., Yₙ` are jointly independent `G`-valued random variables,
then `d[Y i₀; μ # ∑ i ∈ s, Y i; μ] ≤ 2 * ∑ i ∈ s, d[Y i₀; μ # Y i; μ]`.-/
lemma kvm_ineq_II {I : Type*} {i₀ : I} {s : Finset I} (hs : ¬ i₀ ∈ s)
    (hs' : Finset.Nonempty s) {Y : I → Ω → G} [∀ i, FiniteRange (Y i)]
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ) :
    d[Y i₀; μ # ∑ i ∈ s, Y i; μ] ≤ 2 * ∑ i ∈ s, d[Y i₀; μ # Y i; μ] := by
  classical
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let φ i : G → G := if i = i₀ then id else - id
  have hφ i : Measurable (φ i) := .of_discrete
  let Y' i : Ω → G := φ i ∘ Y i
  have mnY : ∀ i, Measurable (Y' i) := fun i ↦ (hφ i).comp (hY i)
  have h_indep2 : IndepFun (Y i₀) (∑ i ∈ s, Y i) μ :=
    h_indep.indepFun_finset_sum_of_notMem (fun i ↦ hY i) hs |>.symm
  have ineq4 : d[Y i₀; μ # ∑ i ∈ s, Y i; μ] + 1/2 * (H[∑ i ∈ s, Y i; μ] - H[Y i₀; μ])
      ≤ ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + 1/2 * (H[Y i; μ] - H[Y i₀; μ])) := by
    calc
      _ = H[Y i₀ - ∑ i ∈ s, Y i ; μ] - H[Y i₀ ; μ] := by
        rw [h_indep2.rdist_eq (hY i₀) (by fun_prop)]
        ring
      _ = H[Y' i₀ + ∑ x ∈ s, Y' x ; μ] - H[Y' i₀ ; μ] := by
        simp [Y', φ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr! 3 with i hi
        simp [ne_of_mem_of_not_mem hi hs, Pi.neg_comp]
      _ ≤ ∑ x ∈ s, (H[Y' i₀ + Y' x ; μ] - H[Y' i₀ ; μ]) := kvm_ineq_I hs mnY (h_indep.comp φ hφ)
      _ = ∑ i ∈ s, (H[Y i₀ - Y i ; μ] - H[Y i₀ ; μ]) := by
        congr! 1 with i hi; simp [Y', φ, ne_of_mem_of_not_mem hi hs, Pi.neg_comp, sub_eq_add_neg]
      _ = _ := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [(h_indep.indepFun (ne_of_mem_of_not_mem hi hs).symm).rdist_eq (hY i₀) (hY i)]
        ring
  replace ineq4 : d[Y i₀; μ # ∑ i ∈ s, Y i; μ] ≤ ∑ i ∈ s, (d[Y i₀; μ # Y i; μ]
      + 1/2 * (H[Y i; μ] - H[Y i₀; μ])) - 1/2 * (H[∑ i ∈ s, Y i; μ] - H[Y i₀; μ]) :=
    le_tsub_of_add_le_right ineq4
  have ineq5 (j : I) (hj : j ∈ s) : H[Y j ; μ] ≤ H[∑ i ∈ s, Y i; μ] :=
    max_entropy_le_entropy_sum hj hY h_indep
  have ineq6 : (s.card : ℝ)⁻¹ * ∑ i ∈ s, (H[Y i; μ] - H[Y i₀; μ]) ≤ H[∑ i ∈ s, Y i; μ] - H[Y i₀; μ] := by
    rw [inv_mul_le_iff₀ (by exact_mod_cast Finset.card_pos.mpr hs'), ← smul_eq_mul,
      Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    gcongr
    exact ineq5 i hi
  have ineq7 : d[Y i₀; μ # ∑ i ∈ s, Y i; μ]
    ≤ ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + (s.card - 1) / (2 * s.card) * (H[Y i; μ] - H[Y i₀; μ])) := by
    calc
      _ ≤ ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + 1/2 * (H[Y i; μ] - H[Y i₀; μ]))
          - 1/2 * (H[∑ i ∈ s, Y i; μ] - H[Y i₀; μ]) := ineq4
      _ ≤ ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + 1/2 * (H[Y i; μ] - H[Y i₀; μ]))
          - 1/2 * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, (H[Y i; μ] - H[Y i₀; μ])) := by gcongr
      _ = ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + 1/2 * (H[Y i; μ] - H[Y i₀; μ])
          - 1/2 * ((s.card : ℝ)⁻¹ * (H[Y i; μ] - H[Y i₀; μ]))) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      _ = ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + (s.card - 1) / (2 * s.card) * (H[Y i; μ] - H[Y i₀; μ])) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [add_sub_assoc, ← mul_assoc, ← sub_mul]
        field_simp
  have ineq8 (i : I) : H[Y i; μ] - H[Y i₀; μ] ≤ 2 * d[Y i₀; μ # Y i; μ] := by
    calc
      _ ≤ |H[Y i₀ ; μ] - H[Y i ; μ]| := by
        rw [← neg_sub]
        exact neg_le_abs _
      _ ≤ 2 * d[Y i₀; μ # Y i; μ] := diff_ent_le_rdist (hY i₀) (hY i)
  calc
    _ ≤ ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + (s.card - 1) / (2 * s.card) * (H[Y i; μ] - H[Y i₀; μ])) :=
      ineq7
    _ ≤ ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + (s.card - 1) / s.card * d[Y i₀; μ # Y i; μ]) := by
      simp_rw [div_eq_mul_inv, mul_inv, mul_comm (2 : ℝ)⁻¹, mul_assoc]
      gcongr ∑ i ∈ s, (d[Y i₀ ; μ # Y i ; μ] + (s.card - 1) * ((s.card : ℝ)⁻¹ * ?_))
      · simp only [sub_nonneg, Nat.one_le_cast]
        exact Nat.one_le_iff_ne_zero.mpr <| Finset.card_ne_zero.mpr hs'
      · exact (inv_mul_le_iff₀ zero_lt_two).mpr (ineq8 _)
    _ ≤ ∑ i ∈ s, (d[Y i₀; μ # Y i; μ] + d[Y i₀; μ # Y i; μ]) := by
      gcongr ∑ i ∈ s, (d[Y i₀ ; μ # Y i ; μ] + ?_) with i
      refine mul_le_of_le_one_left (rdist_nonneg (hY i₀) (hY i)) ?_
      exact (div_le_one (Nat.cast_pos.mpr <| Finset.card_pos.mpr hs')).mpr (by simp)
    _ = 2 * ∑ i ∈ s, d[Y i₀ ; μ # Y i ; μ] := by
      ring_nf
      exact (Finset.sum_mul ..).symm

lemma kvm_ineq_III_aux {X Y Z : Ω → G} [FiniteRange X] [FiniteRange Y]
    [FiniteRange Z] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h_indep : iIndepFun ![X, Y, Z] μ) :
    d[X; μ # Y + Z; μ] ≤ d[X; μ # Y; μ] + (2 : ℝ)⁻¹ * (H[Y + Z; μ] - H[Y; μ]) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have h_indep1 : IndepFun X (Y + Z) μ := by
    convert h_indep.indepFun_add_right (fun i ↦ ?_) 0 1 2 (by simp) (by simp)
    fin_cases i <;> assumption
  have h_indep2 : IndepFun X Y μ := h_indep.indepFun (show 0 ≠ 1 by simp)
  rw [h_indep1.rdist_eq hX (hY.add hZ), h_indep2.rdist_eq hX hY]
  simp only [tsub_le_iff_right, ge_iff_le]
  ring_nf
  rw [sub_add_eq_add_sub, add_sub_assoc, ← tsub_le_iff_left]
  refine kaimanovich_vershik' h_indep hX hY hZ

/-- strengthen the above lemma by not requiring `X` to be independent of `Y`, `Z`. -/
lemma kvm_ineq_III_aux' {X Y Z : Ω → G} [FiniteRange X] [FiniteRange Y]
    [FiniteRange Z] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h_indep : IndepFun Y Z μ) [IsProbabilityMeasure μ] :
  d[X; μ # Y + Z; μ] ≤ d[X; μ # Y; μ] + (2 : ℝ)⁻¹ * (H[Y + Z; μ] - H[Y; μ]) := by
    obtain ⟨Ω', hΩ', μ', X', Y', Z', hprob, h_indep', hX', hY', hZ', hident_X, hident_Y, hident_Z, hfin_X, hfin_Y, hfin_Z⟩ := independent_copies3_nondep_finiteRange hX hY hZ μ μ μ
    -- the argument below could be extracted into a Mathlib lemma
    have hident_YZ : IdentDistrib (⟨Y',Z'⟩) (⟨Y,Z⟩) μ' μ := {
      aemeasurable_fst := by fun_prop
      aemeasurable_snd := by fun_prop
      map_eq := by
        replace h_indep' : IndepFun Y' Z' μ' := h_indep'.indepFun (show 1 ≠ 2 by simp)
        rw [indepFun_iff_map_prod_eq_prod_map_map] at h_indep h_indep' <;> try fun_prop
        rw [h_indep, h_indep']; congr 1
        . exact hident_Y.map_eq
        exact hident_Z.map_eq
    }
    replace hident_YZ : IdentDistrib (Y' + Z') (Y + Z) μ' μ := by convert hident_YZ.comp measurable_add
    rw [←IdentDistrib.rdist_congr hident_X hident_Y, ←IdentDistrib.rdist_congr hident_X hident_YZ,
        ←IdentDistrib.entropy_congr hident_Y, ←IdentDistrib.entropy_congr hident_YZ]
    apply kvm_ineq_III_aux _ _ _ h_indep' <;> fun_prop



/-- If `n ≥ 1` and `X, Y₁, ..., Yₙ`$ are jointly independent `G`-valued random variables,
then `d[Y i₀, ∑ i, Y i] ≤ d[Y i₀, Y i₁] + 2⁻¹ * (H[∑ i, Y i] - H[Y i₁])`.
-/
lemma kvm_ineq_III {I : Type*} {i₀ i₁ : I} {s : Finset I}
    (hs₀ : ¬ i₀ ∈ s) (hs₁ : ¬ i₁ ∈ s) (h01 : i₀ ≠ i₁)
    (Y : I → Ω → G) [∀ i, FiniteRange (Y i)]
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ) :
    d[Y i₀; μ # Y i₁ + ∑ i ∈ s, Y i; μ]
      ≤ d[Y i₀; μ # Y i₁; μ] + (2 : ℝ)⁻¹ * (H[Y i₁ + ∑ i ∈ s, Y i; μ] - H[Y i₁; μ]) := by
  let J := Fin 3
  let S : J → Finset I := ![{i₀}, {i₁}, s]
  have h_dis : Set.univ.PairwiseDisjoint S := by
    intro j _ k _ hjk
    change Disjoint (S j) (S k)
    fin_cases j <;> fin_cases k <;> try exact (hjk rfl).elim
    all_goals
      simp_all [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Finset.disjoint_singleton_right, S, h01.symm]
  let φ : (j : J) → ((_ : S j) → G) → G
    | 0 => fun Ys ↦ Ys ⟨i₀, by simp [S]⟩
    | 1 => fun Ys ↦ Ys ⟨i₁, by simp [S]⟩
    | 2 => fun Ys ↦ ∑ i : s, Ys ⟨i.1, i.2⟩
  have hφ : (j : J) → Measurable (φ j) := fun j ↦ .of_discrete
  have h_indep' : iIndepFun ![Y i₀, Y i₁, ∑ i ∈ s, Y i] μ := by
    convert iIndepFun.finsets_comp S h_dis h_indep hY φ hφ with j x
    fin_cases j <;> simp [φ, (s.sum_attach _).symm]
  exact kvm_ineq_III_aux (hY i₀) (hY i₁) (by fun_prop) h_indep'

open Classical

private theorem entropy_kvm_step {Ω : Type u_1} {G : Type u_5} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [hG : MeasurableSpace G] [inst : MeasurableSingletonClass G] [inst_1 : AddCommGroup G] [inst_2 : Countable G]
  {I : Type*} {s t : Finset I} (hdisj : Disjoint s t) {X : I → Ω → G}
  (hX : ∀ (i : I), Measurable (X i)) [∀ (i : I), FiniteRange (X i)]
  (hindep : iIndepFun X μ)
  (f : I → I) (hf : Finset.image f t ⊆ s) (i : I) (hi : i ∈ t) :
  H[-∑ i ∈ s \ {f i}, X i + -X (f i) + X i ; μ] - H[-∑ i ∈ s \ {f i}, X i + -X (f i) ; μ] ≤
    H[-X (f i) + X i ; μ] - H[-X (f i) ; μ] := by
  apply kaimanovich_vershik
  · set S : Fin 3 → Finset I := ![s \ {f i}, {f i}, {i}] with hS
    set φ : (j : Fin 3) → (i : {k : I // k ∈ S j} → G) → G :=
      fun j => match j with
    | 0 => fun Y => - ∑ l : (S 0).attach, Y l
    | 1 => fun Y => - Y ⟨f i, Finset.mem_singleton.mpr rfl⟩
    | 2 => fun Y => Y ⟨i, Finset.mem_singleton.mpr rfl⟩
    with hφ
    have s_disj : Set.univ.PairwiseDisjoint S := by
      rw [hS, show (Set.univ : Set <| Fin 3) = insert 0 (insert 1 {2}) by ext x; fin_cases x <;> simp]
      apply Set.PairwiseDisjoint.insert (Set.PairwiseDisjoint.insert _ _)
      · intro j hj hj'
        have hj_mem : j ∈ ({1, 2} : Finset _) := by simp_all
        have := Finset.disjoint_right.mp hdisj hi
        fin_cases hj_mem <;> aesop
      simp_rw [Set.pairwiseDisjoint_singleton]
      intro j hj hj'
      have : i ≠ f i := by
        intro h
        exact Finset.disjoint_right.mp hdisj hi (h ▸ (hf (Finset.mem_image_of_mem f hi)))
      simp [Set.mem_singleton_iff.mp hj, this]
    have := iIndepFun.finsets_comp S s_disj hindep hX φ (fun j => by
      fin_cases j <;> simp only [hφ] <;> fun_prop)
    suffices (fun j a ↦ φ j fun i ↦ X (↑i) a) = ![-∑ i ∈ s \ {f i}, X i, -X (f i), X i] by
      rwa [←this]
    rw [hφ]
    ext x a : 2
    fin_cases x <;> simp; rw [hS]; simp [Finset.sum_attach (s \ {f i}).attach  (X · a), Finset.sum_attach (s \ {f i}) (X · a)]
  · convert Finset.measurable_sum (s \ {f i}) (fun i _ => (hX i).neg)
    simp [Pi.neg_apply, Finset.sum_apply, Finset.sum_neg_distrib]
  · apply (hX <| f i).neg
  · apply hX

private theorem entropy_sum_le_entropy_neg_add {I : Type*} {s t : Finset I} (hdisj : Disjoint s t)
  (X : I → Ω → G) (hX : ∀ (i : I), Measurable (X i)) [∀ (i : I), FiniteRange (X i)]
  (hindep : iIndepFun X μ)
  (W_meas : Measurable (∑ i ∈ s, X i)) (U_meas : Measurable (∑ i ∈ t, X i)) :
  H[∑ i ∈ t, X i ; μ] ≤ H[-(∑ i ∈ s, X i) + ∑ i ∈ t, X i ; μ] := by
  haveI : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  rw [neg_add_eq_sub]
  apply le_trans (le_max_left H[∑ i ∈ t, X i ; μ] H[∑ i ∈ s, X i ; μ])
  apply ProbabilityTheory.max_entropy_le_entropy_sub U_meas W_meas
    <| IndepFun.finsetSum hindep hX hdisj.symm

private theorem kvm_decomposition_indep_helper {Ω : Type u_1} {G : Type u_5} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [hG : MeasurableSpace G] [inst : MeasurableSingletonClass G] [inst_1 : AddCommGroup G] [inst_2 : Countable G]
  {I : Type*} {s t : Finset I} (hdisj : Disjoint s t) (X : I → Ω → G)
  (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
  (W : Ω → G) (hW : W = ∑ i ∈ s, X i) (W_meas : Measurable W)
  (Y : Option { x // x ∈ t } → Ω → G)
  (hY : Y = fun i ↦ match i with | some i => X ↑i | none => -W)
  (Y_meas : ∀ i, Measurable (Y i))
  (Y_finite : ∀ i, FiniteRange (Y i)) :
  iIndepFun Y μ := by
  set S : Option {x // x ∈ t} → Finset I := fun i => match i with | some i => {i.val} | none => s with hS
  set φ : I → G → G := fun i ↦ if i ∈ t then id else - id with hφ
  set X' : I → Ω → G := fun i ↦ φ i ∘ X i with hX'
  have h_disjoint : Set.PairwiseDisjoint Set.univ S := by
    intro i _ j _ hij
    match i, j with
    | some i, some j =>
      simp only [hS]
      intro a b ; simp_all ; aesop
    | some i, none =>
      simp only [hS, Finset.disjoint_singleton_left]
      simp_all only [Set.mem_univ, ne_eq, reduceCtorEq, not_false_eq_true]
      obtain ⟨val, property⟩ := i
      exact Finset.disjoint_right.mp hdisj property
    | none, some j => simpa [hS, Function.onFun] using Finset.disjoint_right.mp hdisj j.property
    | none, none => exact (hij rfl).elim
  have h_sum : Y = (fun (j : Option {x // x ∈ t}) ↦ (fun a ↦ ∑ i ∈ S j, X' i a)) := by
    rw [hY, hS]
    ext j a
    match j with
    | some i => simp [Finset.sum_singleton, hX', hφ]
    | none =>
      simp only [Pi.neg_apply, Finset.sum_apply, hX', hφ, hW, ←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [if_neg]
      simp
      apply Finset.disjoint_left.mp hdisj hx
  rw [h_sum]
  apply iIndepFun.finsetSum _ h_disjoint
  apply iIndepFun.comp hindep
  all_goals
    intro i
    by_cases hi : i ∈ t <;> measurability

private theorem entropy_kvm_decomposition {I : Type*} {s t : Finset I} (hdisj : Disjoint s t)
    (X : I → Ω → G) (hX : ∀ (i : I), Measurable (X i))
    [∀ (i : I), FiniteRange (X i)] (hindep : iIndepFun X μ) :
    H[-(∑ i ∈ s, X i) + ∑ i ∈ t, X i ; μ] ≤ H[-(∑ i ∈ s, X i) ; μ]
      + ∑ i ∈ t, (H[-(∑ i ∈ s, X i) + X i ; μ] - H[-(∑ i ∈ s, X i) ; μ]) := by
  haveI : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  set W := ∑ i ∈ s, X i with hW_def
  set U := ∑ i ∈ t, X i with hU_def
  set Y : Option {x // x ∈ t} → Ω → G := fun i => match i with| some i => X i | none => - W with hY
  have W_meas : Measurable W := by
    convert Finset.measurable_sum s (fun i _ => hX i)
    simp only [hW_def, Finset.sum_apply]
  have Y_meas : ∀ i, Measurable (Y i)
    | some i => by simpa only [hY] using hX i
    | none => by simpa only [hY] using W_meas.neg
  have this (i) : FiniteRange (Y i) := by
    match i with | some i => simp only [hY]; infer_instance | none => simp only [hY]; infer_instance
  have Y_indep : iIndepFun Y μ := by
    apply kvm_decomposition_indep_helper hdisj X hX hindep W hW_def W_meas Y hY Y_meas
    exact fun i => by infer_instance
  have kvm := kvm_ineq_I (show none ∉ t.attach.image some by aesop) Y_meas Y_indep
  have lem₁ : ∑ i ∈ t.attach.image some, Y i = ∑ i ∈ t, X i := by
    rw [Finset.sum_image, Finset.sum_attach]
    intro x hx y hy hxy
    apply Option.some.inj hxy
  have lem₂ : ∑ x ∈ t.attach, (H[Y none + Y (some x) ; μ] - H[Y none ; μ])
      = ∑ i ∈ t, (H[-W + X i; μ] - H[-W ; μ]) :=
    calc
      _ = ∑ x ∈ t.attach, (fun i : I => H[-W + X i; μ] - H[-W ; μ]) x.val := by
          simp [hY]
      _ = ∑ i ∈ t, (H[-W + X i ; μ] - H[-W ; μ]) := by
          rw [t.sum_attach (fun i : I => H[-W + X i; μ] - H[-W ; μ])]
  rw [lem₁, Finset.sum_image (fun x hx y hy =>  Option.some.inj), lem₂, tsub_le_iff_right,
    add_comm _ (H[Y none ; μ])] at kvm
  simpa [hY, ← hU_def, ← hW_def] using kvm

/-- Let `X₁, ..., Xₘ` and `Y₁, ..., Yₗ` be tuples of jointly independent random variables (so the
`X`'s and `Y`'s are also independent of each other), and let `f: {1,..., l} → {1,... ,m}` be a
function, then `H[∑ j, Y j] ≤ H[∑ i, X i] + ∑ j, H[Y j - X f(j)] - H[X_{f(j)}]`.-/
lemma ent_of_sum_le_ent_of_sum {I:Type*} {s t : Finset I} (hdisj : Disjoint s t)
    (X : I → Ω → G) (hX : ∀ i, Measurable (X i)) [∀ i, FiniteRange (X i)]
    (hindep : iIndepFun X μ ) (f : I → I) (hf : Finset.image f t ⊆ s) :
    H[∑ i ∈ t, X i; μ] ≤ H[∑ i ∈ s, X i; μ] + ∑ i ∈ t, (H[ X i - X (f i); μ] - H[X (f i); μ]) := by
  --Write `W := $W := ∑_{i=1}^m X_i$`
  set W := ∑ i ∈ s, X i with hW
  --Write `U := ∑_{j=1}^l Y_j` (in the notation of the informal proof)
  set U := ∑ i ∈ t, X i with hU
  haveI : FiniteRange U := .finsum X
  haveI : FiniteRange W := .finsum X
  have U_meas : Measurable U := by
    convert Finset.measurable_sum t (fun i _ => hX i)
    simp only [hU, Finset.sum_apply]
  have W_meas : Measurable W := by
    convert Finset.measurable_sum s (fun i _ => hX i)
    simp only [hW, Finset.sum_apply]
  calc
    --We have `H[U] ≤ H[-W + U]`
    _ ≤ H[-W + U ; μ ] := entropy_sum_le_entropy_neg_add hdisj X hX hindep W_meas U_meas
      -- `≤ H[-W] + ∑_{j=1}^l (H[-W + Y_j] - H[-W])`
    _ ≤ H[-W ; μ] + ∑ i ∈ t, (H[-W + X i ; μ] - H[-W ; μ]) := by
      apply entropy_kvm_decomposition hdisj
      -- We'd want to give those to `apply` but this leads to timeouts...
      apply hX
      apply hindep
    _ ≤ H[-W ; μ] + ∑ i ∈ t, (H[X i - X (f i) ; μ] - H[X (f i) ; μ]) := by
      rw [add_le_add_iff_left]
      apply Finset.sum_le_sum
      intro i hi
      calc
        H[-W + X i ; μ] - H[-W ; μ] = H[(- ∑ i ∈ s \ {f i}, X i) + (- (X (f i))) + X i; μ] - H[(- ∑ i ∈ s \ {f i}, X i) + (- (X (f i))) ; μ]:= by
          congr 3
          all_goals
            rw [hW, Finset.sum_sdiff_eq_sub, Finset.sum_singleton, neg_sub]
            · abel
            · rw [Finset.singleton_subset_iff]
              apply hf (Finset.mem_image_of_mem _ hi)
        _ ≤ H[(- (X <| f i)) + X i ; μ] - H[- (X (f i)) ; μ] :=
          entropy_kvm_step hdisj hX hindep f hf i hi
        _ = H[(- (X <| f i)) + X i ; μ] - H[(X (f i)) ; μ] := by
          rw [ProbabilityTheory.entropy_neg (hX <| f i)]
      apply le_of_eq
      congr
      abel
    _ = H[W ; μ] + ∑ i ∈ t, (H[X i - X (f i); μ] - H[X (f i); μ]) := by
      rw [ProbabilityTheory.entropy_neg]
      measurability

open Classical in

/-- Let `X,Y,X'` be independent `G`-valued random variables, with `X'` a copy of `X`,
and let `a` be an integer. Then `H[X - (a+1)Y] ≤ H[X - aY] + H[X - Y - X'] - H[X]` -/
lemma ent_sub_zsmul_le {Y : Ω → G} {X' : Ω → G} [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (h_indep : iIndepFun ![X, Y, X'] μ) (hident : IdentDistrib X X' μ μ) {a : ℤ} :
    H[X - (a+1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] := by
  rw [add_smul, one_smul, add_comm, sub_add_eq_sub_sub]
  have iX'Y : IndepFun X' Y μ := h_indep.indepFun (show 2 ≠ 1 by simp)
  have iXY : IndepFun X Y μ := h_indep.indepFun (show 0 ≠ 1 by simp)
  have hident' : IdentDistrib (X' - a • Y) (X - a • Y) μ μ := by
    simp_rw [sub_eq_add_neg]
    apply hident.symm.add (.refl (hY.const_smul a).neg.aemeasurable)
    · convert iX'Y.comp measurable_id (.of_discrete (f := fun y ↦ -(a • y))) using 1
    · convert iXY.comp measurable_id (.of_discrete (f := fun y ↦ -(a • y))) using 1
  have iXY_X' : IndepFun (⟨X, Y⟩) X' μ :=
    h_indep.indepFun_prodMk (fun i ↦ (by fin_cases i <;> assumption)) 0 1 2
      (show 0 ≠ 2 by simp) (show 1 ≠ 2 by simp)
  calc
    _ ≤ H[X - Y - X' ; μ] + H[X' - a • Y ; μ] - H[X' ; μ] := by
      refine ent_of_diff_le _ _ _ (hX.sub hY) (hY.const_smul a) hX' ?_
      exact iXY_X'.comp (φ := fun (x, y) ↦ (x - y, a • y)) .of_discrete measurable_id
    _ = _ := by
      rw [hident.entropy_congr]
      simp only [add_comm, sub_left_inj, _root_.add_left_inj]
      exact hident'.entropy_congr

/-- Let `X,Y,X'` be independent `G`-valued random variables, with `X'` a copy of `X`,
and let `a` be an integer. Then `H[X - (a+1)Y] ≤ H[X - aY] + H[X - Y - X'] - H[X]` -/
lemma ent_sub_nsmul_le {Y : Ω → G} {X' : Ω → G} [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (h_indep : iIndepFun ![X, Y, X'] μ) (hident : IdentDistrib X X' μ μ) {a : ℕ} :
    H[X - (a + 1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] :=
  mod_cast ent_sub_zsmul_le hX hY hX' h_indep hident (a := a)

/-- Let `X,Y,X'` be independent `G`-valued random variables, with `X'` a copy of `X`,
and let `a` be an integer. Then `H[X - (a-1)Y] ≤ H[X - aY] + H[X - Y - X'] - H[X]` -/
lemma ent_of_sub_smul' {Y : Ω → G} {X' : Ω → G} [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (hX': Measurable X')
    (h_indep : iIndepFun ![X, Y, X'] μ) (hident : IdentDistrib X X' μ μ) {a : ℤ} :
    H[X - (a-1) • Y; μ] ≤ H[X - a • Y; μ] + H[X - Y - X'; μ] - H[X; μ] := by
  rw [sub_smul, one_smul, sub_eq_add_neg, neg_sub, add_sub]
  have iX'Y : IndepFun X' Y μ := h_indep.indepFun (show 2 ≠ 1 by simp)
  have iXY : IndepFun X Y μ := h_indep.indepFun (show 0 ≠ 1 by simp)
  have hident' : IdentDistrib (X' - a • Y) (X - a • Y) μ μ := by
    simp_rw [sub_eq_add_neg]
    apply hident.symm.add (.refl (hY.const_smul a).neg.aemeasurable)
    · convert iX'Y.comp measurable_id (.of_discrete (f := fun y ↦ -(a • y))) using 1
    · convert iXY.comp measurable_id (.of_discrete (f := fun y ↦ -(a • y))) using 1
  have hident'' : IdentDistrib (-(X + Y - X')) (X - Y - X') μ μ := by
    simp_rw [neg_sub, ← sub_sub, sub_eq_add_neg, add_assoc]
    refine hident.symm.add ?_ ?_ ?_
    rotate_left
    · rw [← neg_add]
      apply IndepFun.comp _ measurable_id measurable_neg
      refine h_indep.indepFun_add_right (fun i ↦ (by fin_cases i <;> assumption))
        2 0 1 (by simp) (by simp)
    · rw [← neg_add]
      apply IndepFun.comp _ measurable_id measurable_neg
      refine h_indep.indepFun_add_right (fun i ↦ (by fin_cases i <;> assumption))
        0 1 2 (by simp) (by simp)
    rw [add_comm, ← neg_add, ← neg_add]
    exact (IdentDistrib.refl hY.aemeasurable).add hident iXY.symm iX'Y.symm |>.neg
  have iXY_X' : IndepFun (⟨X, Y⟩) X' μ :=
    h_indep.indepFun_prodMk (fun i ↦ (by fin_cases i <;> assumption)) 0 1 2
      (show 0 ≠ 2 by simp) (show 1 ≠ 2 by simp)
  calc
    _ ≤ H[X + Y - X' ; μ] + H[X' - a • Y ; μ] - H[X' ; μ] := by
      refine ent_of_diff_le _ _ _ (hX.add hY) (hY.const_smul a) hX' ?_
      exact iXY_X'.comp (φ := fun (x, y) ↦ (x + y, a • y)) .of_discrete measurable_id
    _ = H[- (X + Y - X') ; μ] + H[X - a • Y ; μ] - H[X ; μ] := by
      rw [hident.entropy_congr]
      simp only [hident'.entropy_congr, add_comm, sub_left_inj, _root_.add_right_inj]
      exact entropy_neg (hX.add hY |>.sub hX') |>.symm
    _ = _ := by
      rw [add_comm, hident''.entropy_congr]

/-- Let `X,Y` be independent `G`-valued random variables, and let `a` be an integer. Then
  `H[X - aY] - H[X] ≤ 4 |a| d[X ; Y]`. -/
lemma ent_sub_zsmul_sub_ent_le {Y : Ω → G} [IsProbabilityMeasure μ] [Fintype G]
    (hX : Measurable X) (hY : Measurable Y) (h_indep : IndepFun X Y μ) {a : ℤ} :
    H[X - a • Y; μ] - H[X; μ] ≤ 4 * |a| * d[X ; μ # Y ; μ] := by
  obtain ⟨Ω', mΩ', μ', X₁', Y', X₂', hμ', h_indep', hX₁', hY', hX₂', idX₁, idY, idX₂⟩
    := independent_copies3_nondep hX hY hX μ μ μ
  have iX₁Y : IndepFun X₁' Y' μ' := h_indep'.indepFun (show 0 ≠ 1 by simp)
  have iYX₂ : IndepFun Y' X₂' μ' := h_indep'.indepFun (show 1 ≠ 2 by simp)
  have iX₂nY : IndepFun X₂' (-Y') μ' := iYX₂.symm.comp measurable_id measurable_neg
  have inX₁YX₂ : iIndepFun ![-X₁', Y', X₂'] μ' := by
    convert h_indep'.comp ![-id, id, id] (by fun_prop) with i
    match i with | 0 => rfl | 1 => rfl | 2 => rfl
  have idX₁X₂' : IdentDistrib X₁' X₂' μ' μ' := idX₁.trans idX₂.symm
  have idX₁Y : IdentDistrib (⟨X, Y⟩) (⟨X₁', Y'⟩) μ μ' :=
    IdentDistrib.prodMk idX₁.symm idY.symm h_indep iX₁Y
  have h1 : H[Y' - X₁' + X₂'; μ'] - H[Y' - X₁'; μ'] ≤ H[Y' + X₂'; μ'] - H[Y'; μ'] := by
    simp_rw [sub_eq_add_neg Y', add_comm Y' (-X₁')]
    exact kaimanovich_vershik inX₁YX₂ hX₁'.neg hY' hX₂'
  have h2 : H[X₁' - Y' - X₂'; μ'] - H[X₁'; μ'] ≤ d[X₁' ; μ' # Y' ; μ'] + d[X₁' ; μ' # -Y' ; μ'] := by
    rw [idX₁X₂'.rdist_congr_left (Y := -Y') hY'.aemeasurable.neg, iX₁Y.rdist_eq hX₁' hY',
      iX₂nY.rdist_eq hX₂' hY'.neg, entropy_neg hY', idX₁X₂'.entropy_congr.symm]
    rw [show H[X₁' - Y' - X₂'; μ'] = H[-(X₁' - Y' - X₂'); μ']
      from entropy_neg (hX₁'.sub hY' |>.sub hX₂') |>.symm]
    rw [show H[X₁' - Y'; μ'] = H[-(X₁' - Y'); μ'] from entropy_neg (hX₁'.sub hY') |>.symm]
    ring_nf
    rw [sub_eq_add_neg, add_comm, add_assoc, sub_neg_eq_add]
    gcongr
    convert sub_le_iff_le_add'.mp h1 using 1
    · simp [sub_eq_add_neg, add_comm]
    · simp only [sub_eq_add_neg, neg_add_rev, neg_neg, add_comm, add_assoc]
      linarith
  have h3 : H[X₁' - Y' - X₂' ; μ'] - H[X₁'; μ'] ≤ 4 * d[X₁' ; μ' # Y' ; μ'] :=
    calc
      _ ≤ d[X₁' ; μ' # Y' ; μ'] + d[X₁' ; μ' # -Y' ; μ'] := h2
      _ ≤ d[X₁' ; μ' # Y' ; μ'] + 3 * d[X₁' ; μ' # Y' ; μ'] := by
        gcongr
        exact rdist_of_neg_le hX₁' hY'
      _ = _ := by ring_nf
  have h4 (a : ℤ) : H[X - (a + 1) • Y; μ] ≤ H[X₁' - a • Y'; μ'] + 4 * d[X₁' ; μ' # Y' ; μ'] := by
    calc
      _ = H[X₁' - (a + 1) • Y'; μ'] :=
        IdentDistrib.entropy_congr <|
          idX₁Y.comp (show Measurable (fun xy ↦ (xy.1 - (a + 1) • xy.2)) by fun_prop)
      _ ≤ H[X₁' - a • Y'; μ'] + H[X₁' - Y' - X₂'; μ'] - H[X₁'; μ'] :=
        ent_sub_zsmul_le hX₁' hY' hX₂' h_indep' idX₁X₂'
      _ ≤ H[X₁' - a • Y'; μ'] + 4 * d[X₁' ; μ' # Y' ; μ'] := by
        rw [add_sub_assoc]
        gcongr
  have h4' (a : ℤ) : H[X - (a - 1) • Y; μ] ≤ H[X₁' - a • Y'; μ'] + 4 * d[X₁' ; μ' # Y' ; μ'] := by
    calc
      _ = H[X₁' - (a - 1) • Y'; μ'] :=
        IdentDistrib.entropy_congr <|
          idX₁Y.comp (show Measurable (fun xy ↦ (xy.1 - (a - 1) • xy.2)) by fun_prop)
      _ ≤ H[X₁' - a • Y'; μ'] + H[X₁' - Y' - X₂'; μ'] - H[X₁'; μ'] :=
        ent_of_sub_smul' hX₁' hY' hX₂' h_indep' idX₁X₂'
      _ ≤ H[X₁' - a • Y'; μ'] + 4 * d[X₁' ; μ' # Y' ; μ'] := by
        rw [add_sub_assoc]
        gcongr
  have (a : ℤ) : H[X₁' - a • Y'; μ'] = H[X - a • Y; μ] :=
    idX₁Y.symm.comp (show Measurable (fun xy ↦ (xy.1 - a • xy.2)) by fun_prop) |>.entropy_congr
  simp_rw [idX₁.rdist_congr idY, this] at h4 h4'
  set n := |a| with ha
  clear_value n
  have hn : 0 ≤ n := by simp [ha]
  lift n to ℕ using hn with n
  induction' n with n ih generalizing a
  · simp [abs_eq_zero.mp ha.symm]
  · have : a ≠ 0 := by
      rw [ne_eq, ← abs_eq_zero, ← ha]
      norm_cast
    have : n = |a - 1| ∨ n = |a + 1| := by
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
          rw [← h]
          exact ih h
        _ = 4 * |a| * d[X ; μ # Y ; μ] := by
          nth_rw 2 [← mul_one 4]
          rw [← add_mul, ← mul_add, ← ha, ← h]
          norm_num
        _ = _ := by rw [← ha]
    · calc
        _ ≤ H[X - (a + 1) • Y; μ] - H[X; μ] + 4 * d[X ; μ # Y ; μ] := by
          nth_rw 1 [(a.add_sub_cancel 1).symm, sub_add_eq_add_sub _ H[X; μ]]
          gcongr
          exact h4' (a + 1)
        _ ≤ 4 * |a + 1| * d[X ; μ # Y ; μ] + 4 * d[X ; μ # Y ; μ] := by
          gcongr
          rw [← h]
          exact ih h
        _ = 4 * |a| * d[X ; μ # Y ; μ] := by
          nth_rw 2 [← mul_one 4]
          rw [← add_mul, ← mul_add, ← ha, ← h]
          norm_num
        _ = _ := by rw [← ha]

/-- Let `X,Y` be independent `G`-valued random variables, and let `a` be a natural number. Then
`H[X - aY] - H[X] ≤ 4 a d[X ; Y]`. -/
lemma ent_sub_nsmul_sub_ent_le {Y : Ω → G} [IsProbabilityMeasure μ] [Fintype G]
    (hX : Measurable X) (hY : Measurable Y) (h_indep : IndepFun X Y μ) {a : ℕ} :
    H[X - a • Y ; μ] - H[X ; μ] ≤ 4 * a * d[X ; μ # Y ; μ] := by
  simpa using ent_sub_zsmul_sub_ent_le hX hY h_indep (a := a)

/-- Let `X,Y` be independent `G`-valued random variables, and let `a` be a natural number. Then
`H[X + aY] - H[X] ≤ 4 a d[X ; Y]`. -/
lemma ent_add_nsmul_sub_ent_le {Y : Ω → G} [IsProbabilityMeasure μ] [Fintype G]
    (hX : Measurable X) (hY : Measurable Y) (h_indep : IndepFun X Y μ) {a : ℕ} :
    H[X + a • Y ; μ] - H[X ; μ] ≤ 4 * a * d[X ; μ # Y ; μ] := by
  simpa using ent_sub_zsmul_sub_ent_le hX hY h_indep (a := -a)

section multiDistance

open Filter Function MeasureTheory Measure ProbabilityTheory

variable {G : Type uG} [hG : MeasurableSpace G] [AddCommGroup G]

/-- Let `X_[m] = (X₁, ..., Xₘ)` be a non-empty finite tuple of `G`-valued random variables `X_i`.
Then we define `D[X_[m]] = H[∑ i, X_i'] - 1/m*∑ i, H[X_i']`, where the `X_i'` are independent copies
of the `X_i`.-/
noncomputable
def multiDist {m : ℕ} {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i))
    (X : ∀ i, (Ω i) → G) : ℝ :=
  H[fun x ↦ ∑ i, x i; .pi (fun i ↦ (hΩ i).volume.map (X i))] - (m:ℝ)⁻¹ * ∑ i, H[X i]

@[inherit_doc multiDist] notation3:max "D[" X " ; " hΩ "]" => multiDist hΩ X

/-- If `X_i` has the same distribution as `Y_i` for each `i`, then `D[X_[m]] = D[Y_[m]]`. -/
lemma multiDist_copy {m : ℕ} {Ω : Fin m → Type*} {Ω' : Fin m → Type*}
    (hΩ : ∀ i, MeasureSpace (Ω i)) (hΩ': ∀ i, MeasureSpace (Ω' i))
    (X : ∀ i, (Ω i) → G) (X' : ∀ i, (Ω' i) → G)
    (hident : ∀ i, IdentDistrib (X i) (X' i)) :
    D[X ; hΩ] = D[X' ; hΩ'] := by
  simp_rw [multiDist, IdentDistrib.entropy_congr (hident _), (hident _).map_eq]

variable [MeasurableSingletonClass G] [Countable G]

/-- Move to Mathlib? -/
@[simp]
theorem MeasureTheory.Measure.map_of_pi {ι:Type*} [Fintype ι]
  {α: ι → Type*} [∀ i, MeasurableSpace (α i)]
  {β: ι → Type*} [∀ i, MeasurableSpace (β i)]
  (μ: ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
  {f: ∀ i, α i → β i} (hf : ∀ i, Measurable (f i)) :
  map (fun x i => f i (x i)) (.pi μ) =
    Measure.pi (fun i => map (f i) (μ i)) := by
    symm; apply pi_eq; intro E hE
    rw [map_apply (by fun_prop) (.univ_pi hE)]
    have : (fun x i ↦ f i (x i)) ⁻¹' Set.univ.pi E = Set.univ.pi (fun i ↦ (f i)⁻¹' (E i)) := by
      aesop
    simp [this]; apply Finset.prod_congr rfl; intro i _
    rw [map_apply (by fun_prop) (hE i)]

/-- If `X_i` are independent, then `D[X_{[m]}] = H[∑_{i=1}^m X_i] - \frac{1}{m} \sum_{i=1}^m H[X_i]`. -/
lemma multiDist_indep {m : ℕ} {Ω : Type*} (hΩ : MeasureSpace Ω) [IsProbabilityMeasure hΩ.volume]
    {X : Fin m → Ω → G} (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X) :
    D[X ; fun _ ↦ hΩ] = H[∑ i, X i] - (∑ i, H[X i]) / m := by
    simp [multiDist, inv_mul_eq_div, entropy]
    congr
    rw [iIndepFun_iff_map_fun_eq_pi_map] at h_indep
    rw [←h_indep, Measure.map_map] <;> try fun_prop
    congr
    . ext ω; simp
    fun_prop


lemma multiDist_nonneg_of_indep [Fintype G] {m : ℕ} {Ω : Type*} (hΩ : MeasureSpace Ω)
    [IsProbabilityMeasure hΩ.volume] (X : Fin m → Ω → G) (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X ℙ) :
    0 ≤ D[X ; fun _ ↦ hΩ] := by
  rw [multiDist_indep hΩ hX h_indep]
  have : IsProbabilityMeasure (ℙ : Measure Ω) := h_indep.isProbabilityMeasure
  by_cases hm : m = 0
  · subst hm
    simp only [Finset.univ_eq_empty, Finset.sum_empty, CharP.cast_eq_zero, div_zero, sub_zero,
      ge_iff_le]
    erw [entropy_const]
  norm_num
  calc
    (∑ i, H[X i]) / m ≤ (∑ i : Fin m, H[∑ i, X i]) / m:= by
      gcongr with i
      convert max_entropy_le_entropy_sum (Finset.mem_univ i) hX h_indep
    _ = H[∑ i, X i] := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- We have `D[X_[m]] ≥ 0`. -/
lemma multiDist_nonneg [Fintype G] {m : ℕ} {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i))
    (hprob : ∀ i, IsProbabilityMeasure (ℙ : Measure (Ω i))) (X : ∀ i, (Ω i) → G)
    (hX : ∀ i, Measurable (X i)) :
    0 ≤ D[X ; hΩ] := by
  obtain ⟨A, _, μA, Y, _, h_indep, hY⟩ := independent_copies' X hX (fun i => ℙ)
  convert multiDist_nonneg_of_indep ⟨μA⟩ Y (fun i => (hY i).1) h_indep using 1
  apply multiDist_copy
  exact fun i => (hY i).2.symm

/-- If `φ : {1, ..., m} → {1, ...,m}` is a bijection, then `D[X_[m]] = D[(X_φ(1), ..., X_φ(m))]`-/
lemma multiDist_of_perm {m : ℕ} {Ω : Fin m → Type*}
    (hΩ : ∀ i, MeasureSpace (Ω i)) (hΩprob : ∀ i, IsProbabilityMeasure (hΩ i).volume)
    (X : ∀ i, (Ω i) → G) (φ : Equiv.Perm (Fin m)) :
    D[fun i ↦ X (φ i); fun i ↦ hΩ (φ i)] = D[X ; hΩ] := by
      simp [multiDist]
      congr 1
      · apply IdentDistrib.entropy_congr
        exact {
          aemeasurable_fst := by fun_prop
          aemeasurable_snd := by fun_prop
          map_eq := by
            let sum := fun x : Fin m → G ↦ ∑ i, x i
            let perm := MeasurableEquiv.piCongrLeft (fun _ ↦ G) φ
            have perm_apply : ∀ (i : Fin m) (x : Fin m → G), perm x i = x (φ.symm i) := by
                  intro i x
                  simp only [perm]
                  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
                  simp only [eq_rec_constant]

            have invar : sum ∘ perm = sum := by
              ext x
              rw [comp_apply]
              convert Finset.sum_bijective φ.symm φ.symm.bijective ?_ ?_
              · simp only [Finset.mem_univ, implies_true]
              intro i _
              rw [perm_apply i x]
            calc
              _ = Measure.map (sum ∘ perm) (.pi fun i ↦ .map (X (φ i)) ℙ) := by rw [invar]
              _ = Measure.map sum (.map perm (.pi fun i ↦ .map (X (φ i)) ℙ)) := by
                rw [Measure.map_map]
                · apply Finset.measurable_sum
                  intro i _
                  exact measurable_pi_apply i
                apply measurable_pi_lambda
                intro i
                have : (fun x : Fin m → G ↦ perm x i) = (fun x : Fin m → G ↦ x (φ.symm i)) := by
                  ext x
                  exact perm_apply i x
                rw [this]
                exact measurable_pi_apply ((Equiv.symm φ) i)
              _ = _ := by
                congr
                exact (MeasureTheory.measurePreserving_piCongrLeft (fun i ↦ .map (X i) ℙ) φ).map_eq
        }
      congr 1
      convert Finset.sum_bijective φ (Equiv.bijective φ) ?_ ?_
      · simp only [Finset.mem_univ, implies_true]
      simp only [Finset.mem_univ, imp_self, implies_true]

/-- The sum of `f` away from the diagonal. -/
abbrev offDiag_sum {m : ℕ} (f : Fin m → Fin m → ℝ) := ∑ j, ∑ k, (if j = k then (0:ℝ) else f j k)

lemma offDiag_sum_left {m : ℕ} (hm : m ≥ 1) (f:Fin m → ℝ) : offDiag_sum (fun j _ ↦ f j) = (m - 1) * ∑ j, f j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.sum_ite]; left
    have : Finset.filter (fun x ↦ ¬j = x)  Finset.univ = Finset.univ.erase j := by aesop
    rw [this, Finset.card_erase_of_mem hj, Finset.card_univ, Fintype.card_fin]
    convert Nat.cast_sub hm
    simp only [Nat.cast_one]

lemma offDiag_sum_right {m : ℕ} (hm : m ≥ 1) (f:Fin m → ℝ) : offDiag_sum (fun _ k ↦ f k) = (m - 1) * ∑ j, f j := by
    rw [← offDiag_sum_left hm f]
    convert Finset.sum_comm using 3 with j hj k hk
    aesop

lemma offDiag_sum_const {m : ℕ} (hm : m ≥ 1) (c : ℝ) : offDiag_sum (m:=m) (fun _ _ ↦ c) = m * (m - 1) * c := by
    rw [offDiag_sum_left hm (fun j => c)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

lemma offDiag_sum_add {m : ℕ} (f g : Fin m → Fin m → ℝ) :
      offDiag_sum (fun j k ↦ f j k + g j k) = offDiag_sum f + offDiag_sum g := by
    convert Finset.sum_add_distrib with j _
    convert Finset.sum_add_distrib using 2 with k _
    by_cases h: j = k
    all_goals simp [h]

lemma offDiag_sum_sub {m : ℕ} (f g : Fin m → Fin m → ℝ) :
      offDiag_sum (fun j k ↦ f j k - g j k) = offDiag_sum f - offDiag_sum g := by
  convert Finset.sum_sub_distrib .. with j _
  convert Finset.sum_sub_distrib .. using 2 with k _
  by_cases h: j = k
  all_goals simp [h]

lemma offDiag_sum_div {m : ℕ} (f : Fin m → Fin m → ℝ) (c : ℝ) :
      offDiag_sum (fun j k ↦ f j k / c) = offDiag_sum f / c := by
    convert (Finset.sum_div _ _ _).symm with j _
    convert (Finset.sum_div _ _ _).symm using 2 with k _
    by_cases h: j = k
    all_goals simp [h]

lemma offDiag_mul_sum {m :ℕ} (f : Fin m → Fin m → ℝ) (c:ℝ) :
      offDiag_sum (fun j k ↦ c * f j k ) = c * offDiag_sum f := by
    convert (Finset.mul_sum _ _ _).symm with j _
    convert (Finset.mul_sum _ _ _).symm using 2 with k _
    by_cases h: j = k
    all_goals simp [h]

lemma offDiag_sum_le {m : ℕ} (f g : Fin m → Fin m → ℝ) (h : ∀ j k, j ≠ k → f j k ≤ g j k) : offDiag_sum f ≤ offDiag_sum g := by
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro k _
    by_cases hjk : j = k
    . simp [hjk]
    simp [hjk, h j k hjk]

/-- To prove multidist_ruzsa_I, we first establish a special case when the random variables are defined on the same space and are jointly independent. -/
lemma multidist_ruzsa_I_indep {m : ℕ} (hm : m ≥ 1) {Ω : Type*} (hΩ : MeasureSpace Ω) [IsProbabilityMeasure (hΩ.volume)]
    (X : Fin m → Ω → G) (h_indep : iIndepFun X) (hmes : ∀ j, Measurable (X j)) (hfin: ∀ j, FiniteRange (X j)) :
    ∑ j, ∑ k, (if j = k then (0:ℝ) else d[X j # -X k]) ≤ m * (m - 1) * D[X; fun _ ↦ hΩ] := by
  have claim1 {j k : Fin m} (h: j ≠ k) : H[X j + X k] ≤ H[∑ i, X i] := by
    set S := ∑ i ∈ {j,k}ᶜ, X i
    have : ∑ i, X i = X j + X k + S := by
      rw [←Finset.sum_compl_add_sum {j,k} _, add_comm]
      congr
      simp [h]
    rw [this]
    apply (le_max_left _ _).trans (max_entropy_le_entropy_add _ _ _)
    . exact Measurable.add (hmes j) (hmes k)
    . have : ∀ i ∈ ({j,k}: Finset (Fin m))ᶜ, Measurable (X i) := by
        intro i _; exact hmes i
      convert Finset.measurable_sum _ this with ω
      simp only [Finset.sum_apply,S]
    set s : Fin 2 → Finset (Fin m) := ![{j,k}, {j,k}ᶜ]
    set γ : Fin 2 → Type uG := fun _ ↦ G
    set ϕ : (j:Fin 2) → (({ x // x ∈ s j } → G) → γ j) := fun _ x ↦ ∑ i, x i
    have hϕ: ∀ a : Fin 2, Measurable (ϕ a) := by
      intro _
      convert Finset.measurable_sum _ _ with ω
      . simp [γ]
        infer_instance
      intro _ _
      measurability

    have h_disjoint: Set.univ.PairwiseDisjoint s := by
      simp [Set.PairwiseDisjoint, Set.Pairwise, Fin.forall_fin_two, Function.onFun, s]

    have hneq : (0:Fin 2) ≠ (1:Fin 2) := by norm_num
    replace h_indep := (h_indep.finsets_comp s h_disjoint hmes ϕ hϕ).indepFun hneq
    simp [s,ϕ] at h_indep
    convert h_indep with ω ω
    . calc
        _ = ∑ i ∈ {j,k}, X i ω := by simp [Finset.sum_pair h]
        _ = _ := by
          convert (Finset.sum_attach _ _).symm
          simp
    simp only [Finset.sum_apply,S]
    exact (Finset.sum_attach _ _).symm


  have claim2 (j k : Fin m) (h: j ≠ k) : d[X j # -X k] ≤ H[∑ i, X i] - (H[X j] + H[X k]) / 2 := by
    rw [IndepFun.rdist_eq _ (hmes j) _]
    . simp only [sub_neg_eq_add, tsub_le_iff_right, entropy_neg (hmes k)]
      convert claim1 h using 1
      ring
    . exact (h_indep.indepFun h).neg_right
    exact (hmes k).neg

  calc
    _ ≤ offDiag_sum (fun j k ↦ (H[∑ i, X i] - (H[X j] + H[X k]) / 2)) := offDiag_sum_le _ _ claim2
    _ = m * (m - 1) * H[∑ i, X i] - ((m - 1) * ∑ j, H[X j] + (m - 1) * ∑ j, H[X j]) / 2 := by
      rw [offDiag_sum_sub, offDiag_sum_div, offDiag_sum_add, offDiag_sum_const hm, offDiag_sum_left hm, offDiag_sum_right hm]
    _ = m * (m - 1) * D[X; fun _ ↦ hΩ] := by
      rw [multiDist_indep hΩ hmes h_indep, mul_sub ((m:ℝ) * ((m:ℝ)-1)) _ _]
      congr
      field_simp
      ring



/-- Let `m ≥ 1`, and let `X_[m]` be a tuple of `G`-valued random variables. Then
  `∑ (1 ≤ j, k ≤ m, j ≠ k), d[X_j; -X_k] ≤ m(m - 1) D[X_[m]].` -/
lemma multidist_ruzsa_I {m : ℕ} (hm : m ≥ 1) {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i))
    {X : ∀ i, (Ω i) → G} (hmes : ∀ j, Measurable (X j))
    (hprob : ∀ j, IsProbabilityMeasure (hΩ j).volume)
    (hfin: ∀ j, FiniteRange (X j)) : ∑ j, ∑ k, (if j = k then (0:ℝ) else d[X j # -X k]) ≤ m * (m - 1) * D[X; hΩ] := by
    obtain ⟨Ω', mΩ', μ', X', hμ', h_indep, hX'⟩
      := independent_copies'_finiteRange X hmes (fun i => ℙ)
    convert multidist_ruzsa_I_indep hm ⟨μ'⟩ X' h_indep (fun i ↦ (hX' i).1) (fun i ↦ (hX' i).2.2) using 1
    . apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro k hk
      by_cases hjk : j = k
      all_goals simp [hjk]
      apply IdentDistrib.rdist_congr
      . exact (hX' j).2.1.symm
      convert IdentDistrib.comp (hX' k).2.1.symm _
      measurability
    congr 1
    apply multiDist_copy
    intro i
    exact (hX' i).2.1.symm

/-- Let `m ≥ 2`, and let `X_[m]` be a tuple of `G`-valued random variables. Then
  `∑ j, d[X_j;X_j] ≤ 2 m D[X_[m]]`. -/
lemma multidist_ruzsa_II {m : ℕ} (hm : m ≥ 2) {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i)) (hprob : ∀ i, IsProbabilityMeasure (hΩ i).volume)
    (X : ∀ i, (Ω i) → G) (hmes : ∀ i, Measurable (X i)) (hfin: ∀ i, FiniteRange (X i)) : ∑ j, d[X j # X j] ≤ 2 * m * D[X; hΩ] := by
      have claim (j k: Fin m) (hjk: j ≠ k) : d[X j # X j] ≤ 2 * d[X j # - X k] := calc
        _ ≤ d[X j # - X k] + d[-X k # X j] := rdist_triangle (hmes j) (Measurable.neg (hmes k)) (hmes j)
        _ = d[X j # - X k] + d[X j # -X k] := by
          congr 1
          apply rdist_symm
        _ = 2 * d[X j # - X k] := by
          ring
      replace claim := offDiag_sum_le _ _ claim
      have hm' : m ≥ 1 := by linarith
      have claim2 : offDiag_sum (fun j k ↦ d[X j # - X k]) ≤ m * (m - 1) * D[X; hΩ] :=
        multidist_ruzsa_I hm' _ hmes hprob hfin
      rw [offDiag_sum_left hm', offDiag_mul_sum] at claim
      have : (m:ℝ) - 1 > 0 := by
        have : (m:ℝ) ≥ 2 := by simp [hm]
        linarith
      calc
        _ = ((m:ℝ)-1)⁻¹ * (m - 1) * ∑ j, d[X j # X j] := by
          field_simp [this]
        _ ≤ ((m:ℝ)-1)⁻¹ * 2 * offDiag_sum fun j k ↦ d[X j # -X k] := by
          rw [mul_assoc, mul_assoc]
          gcongr
        _ ≤ ((m:ℝ)-1)⁻¹ * 2 * (m * (m - 1) * D[X ; hΩ]) := by
          gcongr
        _ = 2 * m * D[X; hΩ] := by
          field_simp [this]
          ring

/-- A version of multidist_ruzsa_III assuming independence. -/
lemma multidist_ruzsa_III' {m : ℕ} (hm : m ≥ 2) {Ω : Type*} {hΩ : MeasureSpace Ω}
    {X : Fin (m + 1) → Ω → G} (hmes : ∀ i, Measurable (X i))
    (hident : ∀ j k, IdentDistrib (X j) (X k)) (hindep : iIndepFun X)
    (hfin : ∀ i, FiniteRange (X i)) [IsProbabilityMeasure (ℙ : Measure Ω)] (i₀ : Fin m) :
    D[Fin.init X ; fun _ ↦ hΩ] ≤ m * d[X i₀.castSucc # X i₀.castSucc] := by
  set m' : Fin (m + 1) := Fin.last _
  set X₀ := X m'
  set S := ∑ i : Fin m, X i.castSucc
  have hent (i : Fin (m + 1)) : H[X i] = H[X₀] := (hident _ _).entropy_congr
  have hind' (i : Fin m) : IndepFun (X i.castSucc) X₀ ℙ := hindep.indepFun <| by simp [m']
  have hind_S : IndepFun S X₀ ℙ := by
    set s : Finset (Fin (m + 1)) := .Iio m'
    set s' : Finset (Fin (m + 1)) := {m'}
    have h_disjoint : Disjoint s s' := by aesop
    have hm': m' ∈ s' := Finset.mem_singleton.mpr rfl
    let φ (x : s → G) : G := ∑ i, x i
    let φ' (x : s' → G) : G := x ⟨m', hm'⟩
    have hφ : Measurable φ := by fun_prop
    have hφ' : Measurable φ' := by fun_prop
    convert hindep.finsets_comp' h_disjoint hmes hφ hφ' with ω
    simp [S, φ, s.sum_attach (X · ω)]
    exact Fin.sum_univ_castSucc' (X · ω)
  have hmes_S : Measurable S := by fun_prop
  calc
    _ = H[S] - (∑ i : Fin m, H[X i.castSucc])/m :=
       multiDist_indep _ (X := Fin.init X) (by intro i; simp [Fin.init]; fun_prop) <| (hindep.precomp <| Fin.castSucc_injective m:)
    _ ≤ H[-X₀ + S] - (∑ i : Fin m, H[X i.castSucc])/m := by
      gcongr
      rw [neg_add_eq_sub]
      exact (le_max_left _ _).trans (max_entropy_le_entropy_sub hmes_S (hmes _) hind_S)
    _ = (H[-X₀ + S] - H[-X₀]) - (∑ i : Fin m, H[X i.castSucc])/m + H[-X₀] := by abel
    _ ≤ ∑ i : Fin m, (H[-X₀ + X i.castSucc] - H[-X₀])
        - (∑ i : Fin m, H[X i.castSucc]) / m + H[-X₀] := by
      gcongr
      set Y : Fin (m + 1) → Ω → G := fun i ↦ if (i = m') then - X₀ else X i
      have hYfin (i : Fin (m + 1)) : FiniteRange (Y i) := by
        by_cases h : i = m' <;> simp [Y, h]
        all_goals infer_instance
      have hYfin (i : Fin (m + 1)) : Measurable (Y i) := by
        by_cases h : i = m' <;> simp [Y, h]
        . exact (hmes _).neg
        . exact hmes i
      have : H[Y m' + ∑ i < m', Y i] - H[Y m'] ≤ ∑ i < m', (H[Y m' + Y i] - H[Y m']) := by
        apply kvm_ineq_I Finset.notMem_Iio_self hYfin _
        set f : Fin (m + 1) → G → G := fun i g ↦ if i = m' then -g else g
        convert iIndepFun.comp hindep f _ with i
        . ext ω
          by_cases h : i = m' <;> simp [f, h, Y, X₀]
        intro i
        by_cases h : i = m' <;> simp [f, h]
        all_goals measurability
      convert this using 1
      . congr
        . simp [Y, X₀]
        . convert Fin.sum_univ_castSucc' Y using 2 with i _
          have : i.castSucc ≠ m' := by simp [m']
          simp [Y, this]
        simp [Y,X₀]
      rw [← Fin.sum_univ_castSucc' _]
      congr; ext i
      have : i.castSucc ≠ m' := by simp [m']
      congr
      all_goals simp [Y,this,X₀]
    _ = ∑ i : Fin m, d[X i.castSucc # X₀] - (∑ i : Fin m, H[X₀])/m + H[-X₀] := by
      congr 2
      . apply Finset.sum_congr rfl
        intro i _
        rw [(hind' i).rdist_eq (hmes _) (hmes _), hent, entropy_neg (hmes _), neg_add_eq_sub]
        linarith
      congr 1; apply Finset.sum_congr rfl
      intro i _; exact hent _
    _ = ∑ i : Fin m, d[X i.castSucc # X₀] := by simp [X₀, entropy_neg (hmes _)]; field_simp
    _ = ∑ i : Fin m, d[X i₀.castSucc # X i₀.castSucc] := by
      congr; ext i
      exact (hident _ _).rdist_congr (hident _ _)
    _ = _ := by simp

/-- Let `I` be an indexing set of size `m ≥ 2`, and let `X_[m]` be a tuple of `G`-valued random
variables. If the `X_i` all have the same distribution, then `D[X_[m]] ≤ m d[X_i;X_i]` for any
`1 ≤ i ≤ m`. -/
lemma multidist_ruzsa_III {m : ℕ} (hm : m ≥ 2) {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i))
    (X : ∀ i, (Ω i) → G) (hident : ∀ j k, IdentDistrib (X j) (X k)) (hmes : ∀ i, Measurable (X i)) (hprob : ∀ i, IsProbabilityMeasure (hΩ i).volume) (hfin: ∀ i, FiniteRange (X i)) (i₀ :Fin m) : D[X; hΩ] ≤ m * d[X i₀ # X i₀] := by
    have hmnon: NeZero m := by rw [neZero_iff]; linarith
    obtain ⟨Ω', mΩ', μ', X', hμ', h_indep, hX'⟩
      := independent_copies'_finiteRange (fun (i : Fin (m + 1)) ↦ X 0) (fun _ ↦ hmes 0) (fun i => ℙ)
    letI hΩ' : MeasureSpace Ω' := ⟨μ'⟩
    have hident' (j k: Fin (m + 1)) : IdentDistrib (X' j) (X' k) := (hX' j).2.1.trans (hX' k).2.1.symm
    have hfin' (j : Fin (m + 1)) : FiniteRange (X' j) := (hX' j).2.2
    have hmes' (j : Fin (m + 1)) : Measurable (X' j) := (hX' j).1
    convert multidist_ruzsa_III' hm hmes' hident' h_indep hfin' i₀ using 1
    . apply multiDist_copy
      intro i
      exact (hident i 0).trans (hX' _).2.1.symm
    congr 1
    apply IdentDistrib.rdist_congr
    all_goals exact (hident i₀ 0).trans (hX' _).2.1.symm

universe u in
set_option maxHeartbeats 300000 in
/-- Let `m ≥ 2`, and let `X_[m]` be a tuple of `G`-valued random
variables. Let `W := ∑ X_i`. Then `d[W;-W] ≤ 2 D[X_i]`. -/
lemma multidist_ruzsa_IV {m : ℕ} (hm : m ≥ 2) {Ω : Type u} [MeasureSpace Ω] (X : Fin m → Ω → G)
    (h_indep : iIndepFun X) (hmes : ∀ i, Measurable (X i)) [IsProbabilityMeasure (ℙ : Measure Ω)]
    (hfin : ∀ i, FiniteRange (X i)) :
    d[∑ i, X i # - ∑ i, X i] ≤ 2 * D[X; fun _ ↦ inferInstance] := by
    set mS₂ : Fin 2 × Fin m → MeasurableSpace G := fun _ ↦ inferInstance
    set mΩ₂ : (i : Fin 2 × Fin m) → MeasurableSpace Ω := fun _ ↦ inferInstance
    obtain ⟨Ω', hΩ', μ', X', hprob', h_indep', hX'⟩ :=
      independent_copies'_finiteRange (mS := mS₂) (mΩ := mΩ₂) (fun i ↦ (X i.2)) (fun i ↦ hmes i.2)
        (fun _ ↦ volume)
    have hX'meas i := (hX' i).1
    letI hΩ' : MeasureSpace Ω' := ⟨μ'⟩
    set W₀ := ∑ i, X' (0, i)
    set W₁ := ∑ i, X' (1, i)
    have hW_ident (a: Fin 2) : IdentDistrib (∑ i, X' (a, i)) (∑ i, X i) := by
      have : IdentDistrib (fun ω i ↦ X' (a, i) ω) (fun ω i ↦ X i ω) := by
        refine IdentDistrib.iprodMk ?_ hprob' inferInstance ?_ h_indep
        . intro i; exact (hX' (a,i)).2.1
        exact h_indep'.precomp (Prod.mk_right_injective a)
      convert IdentDistrib.comp this (u := fun x ↦ ∑ i, x i) (by measurability)
      all_goals ext ω; simp
    have hW₀_ident : IdentDistrib W₀ (∑ i, X i) := hW_ident 0
    have hW₁_ident : IdentDistrib W₁ (∑ i, X i) := hW_ident 1
    have hW₀_mes : Measurable W₀ := by fun_prop
    have hW₁_mes : Measurable W₁ := by fun_prop
    have hW₀W₁ : H[W₁] = H[W₀] := (hW₁_ident.trans hW₀_ident.symm).entropy_congr
    have hfin' (i : Fin 2 × Fin m) : FiniteRange (X' i) := (hX' i).2.2
    have hmes' (i : Fin 2 × Fin m) : Measurable (X' i) := (hX' i).1

    have claim (a b : Fin m) (hab : a ≠ b) : H[W₀ + W₁] ≤ 3 * H[W₀] - H[X a] - H[X b] := by
      set W₀' := ∑ i ∈ Finset.univ.erase a, X' (0, i)
      set W₁' := ∑ i ∈ Finset.univ.erase b, X' (1, i)
      have hW₀' : W₀ = W₀' + X' (0, a) := (Finset.sum_erase_add _ _ (Finset.mem_univ a)).symm
      have hW₁' : W₁ = X' (1, b) + W₁' := by
        rw [add_comm]
        exact (Finset.sum_erase_add _ _ (Finset.mem_univ b)).symm
      have hW₀'_mes : Measurable W₀' := by fun_prop
      have hW₁'_mes : Measurable W₁' := by fun_prop
      have h1a : H[W₀' + X' (0,a)] = H[W₀] := by rw [hW₀']
      have h1b : H[W₀ + W₁] = H[W₀' + X' (0, a) + W₁] := by rw [hW₀']
      have h1c : H[X' (1, b) + W₁'] = H[W₁] := by rw [hW₁']
      have h1d : H[X' (0, a) + W₁] = H[X' (0, a) + X' (1, b) + W₁'] := by rw [hW₁', add_assoc]

      have h2a : H[X' (0,a)] = H[X a] := by apply IdentDistrib.entropy_congr (hX' (0,a)).2.1
      have h2b : H[X' (1, b)] = H[X b] := by apply IdentDistrib.entropy_congr (hX' (1, b)).2.1
      have h2c : H[X' (0, a) + X' (1, b)] = H[X a + X b] := by
        apply IdentDistrib.entropy_congr
        apply (hX' (0,a)).2.1.add (hX' (1, b)).2.1
        . apply h_indep'.indepFun; simp
        apply h_indep.indepFun; simp [hab]
      have h2d: H[X' (0, a) + X' (0, b)] = H[X a + X b] := by
        apply IdentDistrib.entropy_congr
        apply (hX' (0,a)).2.1.add (hX' (0, b)).2.1
        . apply h_indep'.indepFun; simp [hab]
        apply h_indep.indepFun; simp [hab]

      have h3: H[X a + X b] ≤ H[W₀] := by
        set W := ∑ i ∈ {a, b}ᶜ, X' (0, i)
        have : W₀ = X' (0, a) + X' (0, b) + W := by
          rw [add_comm]
          convert (Finset.sum_compl_add_sum {a, b} (fun a ↦ X' (0,a))).symm using 2
          simp [hab]
        rw [this, ←h2d]
        apply (le_max_left _ _).trans (max_entropy_le_entropy_add _ _ _)
        . fun_prop
        . fun_prop
        set S : Finset (Fin 2 × Fin m) := {(0,a), (0, b)}
        set ι : Fin m ↪ Fin 2 × Fin m := Function.Embedding.sectR (0:Fin 2) (Fin m)
        set S' : Finset (Fin 2 × Fin m) := Finset.map ι {a, b}ᶜ
        have hab' : ((0:Fin 2),a) ≠ (0, b) := by simp [hab]
        have h_disjoint : Disjoint S S' := by
          rw [Finset.disjoint_left]; intro ⟨i, j⟩ h; simp [S,S',ι] at h ⊢; tauto
        set φ : (S → G) → G := fun x ↦ ∑ i, x i
        set φ' : (S' → G) → G := fun x ↦ ∑ i, x i
        have hφ : Measurable φ := by
          apply Finset.measurable_sum
          intro i _; exact measurable_pi_apply i
        have hφ' : Measurable φ' := by
          apply Finset.measurable_sum
          intro i _; exact measurable_pi_apply i
        convert iIndepFun.finsets_comp' h_disjoint h_indep' hmes' hφ hφ' using 1
        . ext ω
          simp [φ]
          rw [Finset.sum_attach S (fun i ↦ X' i ω)]
          simp [S]
          rw [Finset.sum_pair hab' (f := fun x ↦ X' x ω)]
        ext ω
        simp only [Finset.sum_apply, Finset.univ_eq_attach, W, φ']
        rw [Finset.sum_attach S' (fun i ↦ X' i ω)]
        simp only [S', Finset.sum_map]
        congr
      have h4a: H[W₀' + X' (0, a) + W₁] - H[W₀' + X' (0, a)] ≤ H[X' (0, a) + W₁] - H[X' (0,a)] := by
        apply kaimanovich_vershik _ hW₀'_mes (hmes' (0,a)) hW₁_mes
        set S : Fin 3 → Finset (Fin 2 × Fin m) :=
          fun i ↦ match i with
          | 0 => Finset.map (Function.Embedding.sectR (0:Fin 2) (Fin m)) (Finset.univ.erase a)
          | 1 => {(0,a)}
          | 2 => Finset.map (Function.Embedding.sectR (1:Fin 2) (Fin m)) Finset.univ
        have h_disjoint01 : Disjoint (S 0) (S 1) := by
          rw [Finset.disjoint_iff_ne]
          intro (i, b) hb (j, c) hc
          simp [S] at hb hc ⊢
          intro _
          have := hb.1 (hb.2.symm)
          rwa [hc.2]
        have h_disjoint02 : Disjoint (S 0) (S 2) := by
          rw [Finset.disjoint_iff_ne]
          intro (i, b) hb (j, c) hc
          simp [S] at hb hc ⊢
          simp [←hb.2, ←hc]
        have h_disjoint12 : Disjoint (S 1) (S 2) := by
          rw [Finset.disjoint_iff_ne]
          intro (i, b) hb (j, c) hc
          simp [S] at hb hc ⊢
          simp [hb.1, ←hc]
        have h_disjoint : Set.PairwiseDisjoint Set.univ S := by
          rw [Set.PairwiseDisjoint, Set.Pairwise]
          simp_rw [Fin.forall_fin_three]
          simp [h_disjoint01, h_disjoint01.symm, h_disjoint02, h_disjoint02.symm, h_disjoint12, h_disjoint12.symm]
        set φ : (j:Fin 3) → ((i:S j) → G) → G := fun j x ↦ ∑ i, x i
        have hφ (j:Fin 3) : Measurable (φ j) := by
          simp only [Finset.univ_eq_attach, φ]
          apply Finset.measurable_sum
          intro i _; exact measurable_pi_apply i
        convert iIndepFun.finsets_comp S h_disjoint h_indep' hmes' φ hφ using 1
        ext j ω
        fin_cases j
        all_goals simp [φ]; rw [Finset.sum_attach _ (fun i ↦ X' i ω)]; simp [S, W₁, W₀']

      have h4b :
          H[X' (0, a) + X' (1, b) + W₁'] - H[X' (0, a) + X' (1, b)]
            ≤ H[X' (1, b) + W₁'] - H[X' (1, b)] := by
        apply kaimanovich_vershik _ (hmes' (0,a)) (hmes' (1, b)) hW₁'_mes
        set S : Fin 3 → Finset (Fin 2 × Fin m) :=
          fun i ↦ match i with
          | 0 => {(0,a)}
          | 1 => {(1, b)}
          | 2 => Finset.map (Function.Embedding.sectR (1:Fin 2) (Fin m)) (Finset.univ.erase b)
        have h_disjoint01 : Disjoint (S 0) (S 1) := by
          rw [Finset.disjoint_iff_ne]
          intro (i, b) hb (j, c) hc
          simp [S] at hb hc ⊢
          simp [hb.1, hc.1]
        have h_disjoint02 : Disjoint (S 0) (S 2) := by
          rw [Finset.disjoint_iff_ne]
          intro (i, b) hb (j, c) hc
          simp [S] at hb hc ⊢
          simp [hb.1, ←hc.2]
        have h_disjoint12 : Disjoint (S 1) (S 2) := by
          rw [Finset.disjoint_iff_ne]
          intro (i,d) hd (j, c) hc
          simp [S] at hd hc ⊢
          intro _
          replace hc := hc.1 hc.2.symm
          contrapose! hc
          rw [←hc, hd.2]
        have h_disjoint : Set.PairwiseDisjoint Set.univ S := by
          rw [Set.PairwiseDisjoint, Set.Pairwise]
          simp_rw [Fin.forall_fin_three]
          simp [h_disjoint01, h_disjoint01.symm, h_disjoint02, h_disjoint02.symm, h_disjoint12, h_disjoint12.symm]
        set φ : (j:Fin 3) → ((i:S j) → G) → G := fun j x ↦ ∑ i, x i
        have hφ (j:Fin 3) : Measurable (φ j) := by
          simp only [Finset.univ_eq_attach, φ]
          apply Finset.measurable_sum
          intro i _; exact measurable_pi_apply i
        convert iIndepFun.finsets_comp S h_disjoint h_indep' hmes' φ hφ using 1
        ext j ω
        fin_cases j
        all_goals simp [φ]; rw [Finset.sum_attach _ (fun i ↦ X' i ω)]; simp [S, W₁']
      linarith
    replace claim := offDiag_sum_le _ _ claim
    have hm' : m ≥ 1 := by linarith
    rw [offDiag_sum_sub, offDiag_sum_sub, offDiag_mul_sum, offDiag_sum_const hm', offDiag_sum_const hm', offDiag_sum_left hm', offDiag_sum_right hm'] at claim
    have claim2 : m * (m - 1) * H[W₀+W₁] - m*(m - 1)*H[W₀] ≤ 2 * m*(m - 1)*H[W₀] - 2 * (m - 1) * ∑ j, H[X j] := by linarith
    have hpos : (m:ℝ) * (m - 1) > 0 := by
      have : (m:ℝ)-1 > 0 := by simp; linarith
      positivity
    apply le_of_mul_le_mul_left _ hpos
    convert claim2 using 1
    . rw [←mul_sub_left_distrib]; congr
      have hW₁_ident' : IdentDistrib (-W₁) (-∑ i, X i)  := by
        convert IdentDistrib.comp hW₁_ident (u := fun x ↦ -x) _
        exact Measurable.neg fun ⦃t⦄ a ↦ a
      rw [IdentDistrib.rdist_congr hW₀_ident.symm hW₁_ident'.symm, IndepFun.rdist_eq _ hW₀_mes _]
      . simp only [sub_neg_eq_add]
        rw [entropy_neg hW₁_mes]
        linarith
      . set S : Finset (Fin 2 × Fin m) := Finset.map (Function.Embedding.sectR (0:Fin 2) (Fin m)) Finset.univ
        set S' : Finset (Fin 2 × Fin m) := Finset.map (Function.Embedding.sectR (1:Fin 2) (Fin m)) Finset.univ
        have h_disjoint : Disjoint S S' := by
          rw [Finset.disjoint_iff_ne]
          intro (i,a) ha (j, b) hb
          simp [S,S'] at ha hb ⊢
          simp [← ha, ←hb]
        set φ : (S → G) → G := fun x ↦ ∑ i, x i
        set φ' : (S' → G) → G := fun x ↦ - ∑ i, x i
        have hφ : Measurable φ := by
          apply Finset.measurable_sum
          intro i _; exact measurable_pi_apply i
        have hφ' : Measurable φ' := by
          apply Measurable.neg
          apply Finset.measurable_sum
          intro i _; exact measurable_pi_apply i
        convert iIndepFun.finsets_comp' h_disjoint h_indep' hmes' hφ hφ' using 1
        . ext ω
          simp only [Finset.sum_apply, Finset.univ_eq_attach, W₀, φ]
          rw [Finset.sum_attach S (fun i ↦ X' i ω)]
          simp [S]
        ext ω
        simp only [Finset.univ_eq_attach, W₁, φ']
        rw [Finset.sum_attach S' (fun i ↦ X' i ω)]
        simp [S']
      exact Measurable.neg hW₁_mes
    rw [multiDist_indep _ hmes h_indep]
    have : H[∑ i, X i] = H[W₀] := by
      apply IdentDistrib.entropy_congr
      exact hW₀_ident.symm
    rw [this]
    field_simp
    ring


/-- If `D[X_[m]]=0`, then for each `i ∈ I` there is a finite subgroup `H_i ≤ G` such that
`d[X_i; U_{H_i}] = 0`. -/
lemma multidist_eq_zero [Fintype G] {m : ℕ} (hm : m ≥ 2) {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i)) (hprob : ∀ i, IsProbabilityMeasure (hΩ i).volume) (X : ∀ i, (Ω i) → G) (hvanish : D[X; hΩ] = 0) (hmes : ∀ i, Measurable (X i)) (hfin: ∀ i, FiniteRange (X i)) : ∀ i, ∃ H : AddSubgroup G, ∃ U : (Ω i) → G, Measurable U ∧ IsUniform H U ∧ d[X i # U] = 0 := by
  have vanish : ∑ j, d[X j # X j] = 0 := by
    apply le_antisymm
    . have := multidist_ruzsa_II hm hΩ hprob X hmes hfin
      simpa [hvanish] using this
    apply Finset.sum_nonneg
    intro j _; exact rdist_nonneg (hmes j) (hmes j)
  rw [Finset.sum_eq_zero_iff_of_nonneg ?_] at vanish
  swap
  . intro j _; exact rdist_nonneg (hmes j) (hmes j)
  intro i
  replace vanish := exists_isUniform_of_rdist_eq_zero (hmes i) (hmes i) $ vanish i $ Finset.mem_univ i
  obtain ⟨H, U, U_mes, U_unif, hdist, hdist'⟩ := vanish
  exact ⟨H, U, U_mes, U_unif, hdist⟩



-- This is probably not the optimal spelling. For instance one could use the `μ "[|" t "]"` notation from Mathlib.ConditionalProbability to simplify the invocation of `cond`
/-- If `X_[m] = (X_1, ..., X_m)` and `Y_[m] = (Y_1, ..., Y_m)` are tuples of random variables,
with the `X_i` being `G`-valued (but the `Y_i` need not be), then we define
`D[X_[m] | Y_[m]] = ∑_{(y_i)_{1 \leq i \leq m}} (∏ i, p_{Y_i}(y_i)) D[(X_i | Y_i = y_i)_{i=1}^m]`
where each `y_i` ranges over the support of `p_{Y_i}` for `1 ≤ i ≤ m`.
-/
noncomputable
def condMultiDist {m : ℕ} {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i)) {S : Type*} [Fintype S]
    (X : ∀ i, (Ω i) → G) (Y : ∀ i, (Ω i) → S) : ℝ := ∑ ω : Fin m → S, (∏ i, ((hΩ i).volume ((Y i) ⁻¹' {ω i})).toReal) * D[X; fun i ↦ ⟨cond (hΩ i).volume (Y i ⁻¹' {ω i})⟩]

@[inherit_doc multiDist] notation3:max "D[" X " | " Y " ; " hΩ "]" => condMultiDist hΩ X Y

/-- Conditional multidistance is unchanged if we apply an injection to the conditioned variables -/
theorem condMultiDist_of_inj {G : Type*} [hG : MeasurableSpace G] [AddCommGroup G] {m : ℕ}
    {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i)) {S : Type*} [Fintype S] {T : Type*}
    [Fintype T] (X : ∀ i, Ω i → G) (Y : ∀ i, Ω i → S) {f : S → T} (hf : Injective f) :
    D[X | fun i ↦ f ∘ (Y i); hΩ] = D[X | fun i ↦ Y i; hΩ] := by
  set e : (Fin m → S) → (Fin m → T) := fun y ↦ f ∘ y

  convert (Fintype.sum_of_injective e (Injective.comp_left hf) ?_ ?_ _ _).symm
  . intro z hz
    convert zero_mul ?_
    rw [Finset.prod_eq_zero_iff]
    simp [e] at hz
    contrapose! hz
    have : ∀ i, ∃ yi, f yi = z i := by
      intro i
      replace hz := hz i (Finset.mem_univ i)
      contrapose! hz
      have : f ∘ Y i ⁻¹' {z i} = ∅ := by aesop
      simp [this]
    obtain ⟨y, hy⟩ := Classical.axiomOfChoice this
    use y
    aesop
  intro s; congr
  all_goals ext; congr; aesop

/-- Conditional multidistance against a constant is just multidistance -/
theorem condMultiDist_of_const {G : Type*} [hG : MeasurableSpace G] [AddCommGroup G] {m : ℕ} {Ω : Fin m → Type*} [hΩ : ∀ i, MeasureSpace (Ω i)] [hprob : ∀ i, IsProbabilityMeasure (hΩ i).volume] {S : Type*} [Fintype S] (c:Fin m → S) (X : ∀ i, (Ω i) → G) : D[X | fun i ↦ fun _ ↦ c i; hΩ] = D[X ; hΩ] := by
  dsimp [condMultiDist]
  rw [Finset.sum_eq_single c]
  . have : ∀ i, (fun _:Ω i ↦ c i) ⁻¹' {c i} = Set.univ := by
      intros; simp only [Set.mem_singleton_iff, Set.preimage_const_of_mem]
    simp [this]
  . intro y _ hy
    convert zero_mul _
    contrapose! hy
    rw [Finset.prod_ne_zero_iff] at hy
    ext i
    replace hy := hy i (Finset.mem_univ i)
    contrapose! hy
    have : (fun _:Ω i ↦ c i) ⁻¹' {y i} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact id (Ne.symm hy)
    simp [this]
  simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/--Conditional multidistance is nonnegative. -/
theorem condMultiDist_nonneg [Fintype G] {m : ℕ} {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i)) (hprob : ∀ i, IsProbabilityMeasure (ℙ : Measure (Ω i))) {S : Type*} [Fintype S] (X : ∀ i, (Ω i) → G) (Y : ∀ i, (Ω i) → S) (hX : ∀ i, Measurable (X i)) : 0 ≤ D[X | Y; hΩ] := by
  dsimp [condMultiDist]
  apply Finset.sum_nonneg
  intro y _
  by_cases h: ∀ i : Fin m, ℙ (Y i ⁻¹' {y i}) ≠ 0
  . apply mul_nonneg
    . apply Finset.prod_nonneg
      intros
      exact ENNReal.toReal_nonneg
    exact multiDist_nonneg (fun i => ⟨ℙ[|Y i ⁻¹' {y i}]⟩)
      (fun i => cond_isProbabilityMeasure (h i)) X hX
  simp only [ne_eq, not_forall, Decidable.not_not] at h
  obtain ⟨i, hi⟩ := h
  apply le_of_eq
  symm
  convert zero_mul ?_
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [hi, ENNReal.toReal_zero]

/-- A technical lemma: can push a constant into a product at a specific term -/
private lemma Finset.prod_mul {α β:Type*} [Fintype α] [DecidableEq α] [CommMonoid β] (f:α → β) (c: β) (i₀ :α) : (∏ i, f i) * c = ∏ i, (if i=i₀ then f i * c else f i) := calc
  _ = (∏ i, f i) * (∏ i, if i = i₀ then c else 1) := by
    congr
    simp only [prod_ite_eq', mem_univ, ↓reduceIte]
  _ = _ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : i = i₀
    . simp [h]
    simp [h]

/-- A technical lemma: a preimage of a singleton of Y i is measurable with respect to the comap of <X i, Y i> -/
private lemma mes_of_comap {Ω S G : Type*} [hG : MeasurableSpace G] [hS : MeasurableSpace S]
    {X : Ω → G} {Y : Ω → S} {s : Set S} (hs : MeasurableSet s) :
    MeasurableSet[(hG.prod hS).comap fun ω ↦ (X ω, Y ω)] (Y ⁻¹' s) :=
  ⟨.univ ×ˢ s, MeasurableSet.univ.prod hs, by ext; simp⟩

/-- A technical lemma: two different ways of conditioning independent variables gives identical distributions -/
private lemma ident_of_cond_of_indep
    {G : Type*} [hG : MeasurableSpace G] [MeasurableSingletonClass G] [Countable G]
    {m : ℕ} {Ω : Type*} [hΩ : MeasureSpace Ω]
    {S : Type*} [Fintype S] [hS : MeasurableSpace S] [MeasurableSingletonClass S]
    {X : Fin m → Ω → G} (hX : (i : Fin m) → Measurable (X i))
    {Y : Fin m → Ω → S} (hY : (i : Fin m) → Measurable (Y i))
    (h_indep : iIndepFun (fun i ↦ ⟨X i, Y i⟩))
    (y : Fin m → S) (i : Fin m) (hy: ∀ i, ℙ (Y i ⁻¹' {y i}) ≠ 0) :
    IdentDistrib (X i) (X i) (cond ℙ (Y i ⁻¹' {y i})) (cond ℙ (⋂ i, Y i ⁻¹' {y i})) where
  aemeasurable_fst := Measurable.aemeasurable (hX i)
  aemeasurable_snd := Measurable.aemeasurable (hX i)
  map_eq := by
    ext s hs
    rw [Measure.map_apply (hX i) hs, Measure.map_apply (hX i) hs]
    let s' : Finset (Fin m) := {i}
    let f' := fun _ : Fin m ↦ X i ⁻¹' s
    have hf' : ∀ i' ∈ s', MeasurableSet[hG.comap (X i')] (f' i') := by
      intro i' hi'
      simp only [Finset.mem_singleton.mp hi']
      exact MeasurableSet.preimage hs (comap_measurable (X i))
    have h := cond_iInter hY h_indep hf' (fun _ _ ↦ hy _) fun _ ↦ .singleton _
    simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, Finset.prod_singleton,
      s'] at h
    exact h.symm

/-- A technical lemma: if a product of probabilities is nonzero, then each probability is
individually non-zero -/
private lemma prob_nonzero_of_prod_prob_nonzero {m : ℕ}
    {Ω : Type*} [hΩ : MeasureSpace Ω]
    {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Y : Fin m → Ω → S} {y : Fin m → S} (hf : ∏ i, (ℙ (Y i ⁻¹' {y i})).toReal ≠ 0) :
    ∀ i, ℙ (Y i ⁻¹' {y i}) ≠ 0 := by
  simp [Finset.prod_ne_zero_iff, ENNReal.toReal_eq_zero_iff, forall_and] at hf
  exact hf.1

/-- If `(X_i, Y_i)`, `1 ≤ i ≤ m` are independent, then
`D[X_[m] | Y_[m]] = H[∑ i, X_i | (Y_1, ..., Y_m)] - 1/m * ∑ i, H[X_i | Y_i]`
-/
lemma condMultiDist_eq {m : ℕ}
    {Ω : Type*} [hΩ : MeasureSpace Ω]
    {S : Type*} [Fintype S] [hS : MeasurableSpace S] [MeasurableSingletonClass S]
    {X : Fin m → Ω → G} (hX : ∀ i, Measurable (X i))
    {Y : Fin m → Ω → S} (hY : ∀ i, Measurable (Y i))
    (h_indep: iIndepFun (fun i ↦ ⟨X i, Y i⟩)) :
    D[X | Y ; fun _ ↦ hΩ] =
      H[fun ω ↦ ∑ i, X i ω | fun ω ↦ (fun i ↦ Y i ω)] - (∑ i, H[X i | Y i])/m := by
  have : IsProbabilityMeasure (ℙ : Measure Ω) := h_indep.isProbabilityMeasure
  let E := fun i (yi:S) ↦ Y i ⁻¹' {yi}
  let E' := fun (y : Fin m → S) ↦ ⋂ i, E i (y i)
  let f := fun (y : Fin m → S) ↦ ∏ i, Measure.real ℙ (E i (y i))

  have f_eq (y: Fin m → S) : f y = (ℙ (E' y)).toReal := calc
     _ = (∏ i, (ℙ (E i (y i)))).toReal := Eq.symm ENNReal.toReal_prod
     _ = (ℙ (⋂ i, (E i (y i)))).toReal := by
      congr
      exact (iIndepFun.meas_iInter h_indep fun _ ↦ mes_of_comap (.singleton _)).symm

  calc
    _ = ∑ y, (f y) * D[X; fun i ↦ ⟨cond ℙ (E i (y i))⟩] := by rfl
    _ = ∑ y, (f y) * (H[∑ i, X i; cond ℙ (E' y)] - (∑ i, H[X i; cond ℙ (E' y)]) / m) := by
      congr with y
      by_cases hf : f y = 0
      . simp only [hf, zero_mul]
      congr 1
      rw [multiDist_copy (fun i ↦ ⟨cond ℙ (E i (y i))⟩)
        (fun _ ↦ ⟨cond ℙ (E' y)⟩) X X
        (fun i ↦ ident_of_cond_of_indep hX hY h_indep y i (prob_nonzero_of_prod_prob_nonzero hf))]
      have : IsProbabilityMeasure ℙ[|E' y] := by
        apply cond_isProbabilityMeasure
        rw [f_eq y, ENNReal.toReal_eq_zero_iff] at hf
        simpa using hf
      exact multiDist_indep _ hX <|
        h_indep.cond hY (prob_nonzero_of_prod_prob_nonzero hf) fun _ ↦ .singleton _
    _ = ∑ y, (f y) * H[∑ i, X i; cond ℙ (E' y)] - (∑ i, ∑ y, (f y) * H[X i; cond ℙ (E' y)])/m := by
      rw [Finset.sum_comm, Finset.sum_div, ← Finset.sum_sub_distrib]
      congr with y
      rw [← Finset.mul_sum, mul_div_assoc, ← mul_sub]
    _ = _ := by
      congr
      · rw [condEntropy_eq_sum_fintype]
        · congr with y; congr
          · calc
              _ = (ℙ (⋂ i, (E i (y i)))).toReal := f_eq y
              _ = _ := by
                congr; ext x
                simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, E,
                  Iff.symm funext_iff]
          · exact Finset.sum_fn Finset.univ fun c ↦ X c
          ext x
          simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, E']
          exact Iff.symm funext_iff
        exact measurable_pi_lambda (fun ω i ↦ Y i ω) hY
      ext i
      calc
        _ = ∑ y, f y * H[X i; cond ℙ (E i (y i))] := by
          congr with y
          by_cases hf : f y = 0
          . simp only [hf, zero_mul]
          congr 1; apply IdentDistrib.entropy_congr
          exact (ident_of_cond_of_indep hX hY h_indep y i
            (prob_nonzero_of_prod_prob_nonzero hf)).symm
        _ = ∑ y ∈ Fintype.piFinset (fun _ ↦ Finset.univ), ∏ i', (ℙ (E i' (y i'))).toReal
                * (if i'=i then H[X i; cond ℙ (E i (y i'))] else 1) := by
          simp only [Fintype.piFinset_univ]
          congr with y; rw [Finset.prod_mul_distrib]
          congr; rw [Fintype.prod_ite_eq']
        _ = _ := by
          convert (Finset.prod_univ_sum (fun _ ↦ Finset.univ)
            (fun (i' : Fin m) (s : S) ↦ (ℙ (E i' s)).toReal *
              if i' = i then H[X i ; ℙ[|E i s]] else 1)).symm
          calc
            _ = ∏ i', if i' = i then H[X i' | Y i'] else 1 := by
              simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]
            _ = _ := by
              congr with i'; by_cases h : i' = i
              · simp only [h, ↓reduceIte, E]
                rw [condEntropy_eq_sum_fintype _ _ _ (hY i)]
                rfl
              · simp only [h, ↓reduceIte, mul_one, E, ← measureReal_def]
                rw [sum_measureReal_preimage_singleton]
                · simp
                · intro i _
                  exact hY _ (measurableSet_singleton i)

/-- If `(X_i, Y_i)`, `1 ≤ i ≤ m` are independent, then `D[X_[m] | Y_[m]] = ∑_{(y_i)_{1 ≤ i ≤ m}} P(Y_i=y_i ∀ i) D[(X_i | Y_i=y_i ∀ i)_{i=1}^m]`
-/
lemma condMultiDist_eq' {m : ℕ} {Ω : Type*} [hΩ : MeasureSpace Ω]
    {S : Type*} [Fintype S] [hS : MeasurableSpace S] [MeasurableSingletonClass S]
    {X : Fin m → Ω → G} (hX : ∀ i, Measurable (X i)) {Y : Fin m → Ω → S}
    (hY : ∀ i, Measurable (Y i))
    (h_indep : iIndepFun (fun i ↦ ⟨X i, Y i⟩)) :
    D[X | Y ; fun _ ↦ hΩ] =
      ∑ y : Fin m → S, (ℙ (⋂ i, (Y i) ⁻¹' {y i})).toReal
        * D[X; fun _ ↦ ⟨cond ℙ (⋂ i, Y i ⁻¹' {y i})⟩] := by
  rw [condMultiDist]
  congr with y
  rw [iIndepFun.meas_iInter h_indep fun _ ↦ mes_of_comap <| .singleton _, ENNReal.toReal_prod]
  by_cases hf : ∏ i : Fin m, (ℙ (Y i ⁻¹' {y i})).toReal = 0
  . simp [hf]
  congr 1
  apply multiDist_copy
  intro _
  apply ident_of_cond_of_indep hX hY h_indep
  exact prob_nonzero_of_prod_prob_nonzero hf

end multiDistance

section multiDistance_chainRule

/-- Let `π : G → H` be a homomorphism of abelian groups and let `X_[m]` be a tuple of jointly
independent `G`-valued random variables. Then `D[X_[m]]` is equal to
`D[X_[m] | π(X_[m])] + D[π(X_[m])] + I[∑ i, X_i : π(X_[m]) ; | ; π(∑ i, X_i)]`
where `π(X_[m]) := (π(X_1), ..., π(X_m))`.
-/
lemma multiDist_chainRule {G H : Type*} [hG : MeasurableSpace G] [MeasurableSingletonClass G]
    [AddCommGroup G] [Fintype G] [hH : MeasurableSpace H]
    [MeasurableSingletonClass H] [AddCommGroup H]
    [Fintype H] (π : G →+ H) {m : ℕ} {Ω : Type*} (hΩ : MeasureSpace Ω)
    {X : Fin m → Ω → G} (hmes : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X) :
    D[X; fun _ ↦ hΩ] = D[X | fun i ↦ π ∘ X i; fun _ ↦ hΩ]
      + D[fun i ↦ π ∘ X i; fun _ ↦ hΩ]
      + I[∑ i, X i : fun ω ↦ (fun i ↦ π (X i ω)) | π ∘ (∑ i, X i)] := by
  have : IsProbabilityMeasure (ℙ : Measure Ω) := h_indep.isProbabilityMeasure
  set S := ∑ i, X i
  set piX := fun ω ↦ (fun i ↦ π (X i ω))
  set avg_HX := (∑ i, H[X i]) / m
  set avg_HpiX := (∑ i, H[π ∘ X i])/m
  set avg_HXpiX := (∑ i, H[X i | π ∘ X i])/m
  have hSmes : Measurable S := by fun_prop
  have hpiXmes : Measurable piX := by
    rw [measurable_pi_iff]
    intro i
    exact Measurable.comp .of_discrete (hmes i)

  have eq1 : I[S : piX | π ∘ S] = H[S | π ∘ S] + H[piX | π ∘ S] - H[⟨S, piX⟩ | π ∘ S] := by
    rw [condMutualInfo_eq hSmes hpiXmes (Measurable.comp .of_discrete hSmes)]

  have eq1a : H[S | π ∘ S] = H[S] - H[π ∘ S] :=
    condEntropy_comp_self hSmes .of_discrete

  have eq1b : H[piX | π ∘ S] = H[piX] - H[π ∘ S] := by
    set g := fun (y : Fin m → H) ↦ ∑ i, y i
    have : π ∘ S = g ∘ piX := by
      ext x
      simp only [comp_apply, Finset.sum_apply, _root_.map_sum, S, g, piX]
    rw [this]
    exact condEntropy_comp_self hpiXmes .of_discrete

  have eq1c : H[⟨S, piX⟩ | π ∘ S] = H[⟨S, piX⟩] - H[π ∘ S] := by
    set g := fun (x : G × (Fin m → H)) ↦ π x.1
    have : π ∘ S = g ∘ ⟨S, piX⟩ := by
      ext x
      simp only [comp_apply, Finset.sum_apply, _root_.map_sum, S, g, piX]
    rw [this]
    apply condEntropy_comp_self (Measurable.prodMk hSmes hpiXmes) .of_discrete

  have eq2 : H[⟨S, piX⟩] = H[piX] + H[S | piX] := chain_rule _ hSmes hpiXmes

  have eq3 : D[X; fun _ ↦ hΩ] = H[S] - avg_HX := multiDist_indep _ hmes h_indep

  have eq4 : D[X | fun i ↦ π ∘ X i; fun _ ↦ hΩ] = H[S | piX] - avg_HXpiX := by
    dsimp [S, piX]
    convert condMultiDist_eq (S := H) hmes _ _
    . exact Fintype.sum_apply _ _
    . intro i
      exact Measurable.comp .of_discrete (hmes i)
    set g : G → G × H := fun x ↦ ⟨x, π x⟩
    change iIndepFun (fun i ↦ g ∘ X i) ℙ
    exact h_indep.comp _ fun _ ↦ .of_discrete

  have eq5: D[fun i ↦ π ∘ X i; fun _ ↦ hΩ] = H[π ∘ S] - avg_HpiX := by
    convert multiDist_indep _ (X := fun i ↦ π ∘ X i) (by fun_prop) _
    . ext _
      simp only [comp_apply, Finset.sum_apply, _root_.map_sum, S]
    apply iIndepFun.comp h_indep
    exact fun _ ↦ .of_discrete

  have eq6: avg_HX = avg_HpiX + avg_HXpiX := by
    dsimp [avg_HX, avg_HpiX, avg_HXpiX]
    rw [← add_div, ← Finset.sum_add_distrib]
    congr with i
    rw [condEntropy_comp_self (hmes i) .of_discrete]
    abel

  linarith only [eq1, eq1a, eq1b, eq1c, eq2, eq3, eq4, eq5, eq6]

/-- Let `π : G → H` be a homomorphism of abelian groups. Let `I` be a finite index set and let
`X_[m]` be a tuple of `G`-valued random variables. Let `Y_[m]` be another tuple of random variables
(not necessarily `G`-valued). Suppose that the pairs `(X_i, Y_i)` are jointly independent of one
another (but `X_i` need not be independent of `Y_i`). Then
`D[X_[m] | Y_[m]] = D[X_[m] ,|, π(X_[m]), Y_[m]] + D[π(X_[m]) ,| , Y_[m]]`
`+ I[∑ i, X_i : π(X_[m]) ; | ; π(∑ i, X_i), Y_[m]]`. -/
lemma cond_multiDist_chainRule {G H : Type*} [hG : MeasurableSpace G] [MeasurableSingletonClass G]
    [AddCommGroup G] [Fintype G]
    [hH : MeasurableSpace H] [MeasurableSingletonClass H] [AddCommGroup H]
    [Fintype H] (π : G →+ H)
    {S : Type*} [Fintype S] [hS : MeasurableSpace S] [MeasurableSingletonClass S]
    {m : ℕ} {Ω : Type*} [hΩ : MeasureSpace Ω]
    {X : Fin m → Ω → G} (hX : ∀ i, Measurable (X i))
    {Y : Fin m → Ω → S} (hY : ∀ i, Measurable (Y i))
    (h_indep : iIndepFun (fun i ↦ ⟨X i, Y i⟩)) :
    D[X | Y; fun _ ↦ hΩ] = D[X | fun i ↦ ⟨π ∘ X i, Y i⟩; fun _ ↦ hΩ]
      + D[fun i ↦ π ∘ X i | Y; fun _ ↦ hΩ]
      + I[∑ i, X i : fun ω ↦ (fun i ↦ π (X i ω)) |
            ⟨π ∘ (∑ i, X i), fun ω ↦ (fun i ↦ Y i ω)⟩] := by
  have : IsProbabilityMeasure (ℙ : Measure Ω) := h_indep.isProbabilityMeasure
  set E' := fun (y : Fin m → S) ↦ ⋂ i, Y i ⁻¹' {y i}
  set f := fun (y : Fin m → S) ↦ (ℙ (E' y)).toReal
  set hΩc : (Fin m → S) → MeasureSpace Ω := fun y ↦ ⟨cond ℙ (E' y)⟩

  calc
    _ = ∑ y, (f y) * D[X; fun _ ↦ hΩc y] := condMultiDist_eq' hX hY h_indep
    _ = ∑ y, (f y) * D[X | fun i ↦ π ∘ X i; fun _ ↦ hΩc y]
        + ∑ y, (f y) * D[fun i ↦ π ∘ X i; fun _ ↦ hΩc y]
        + ∑ y, (f y) * I[∑ i, X i : fun ω ↦ (fun i ↦ π (X i ω)) |
          π ∘ (∑ i, X i); (hΩc y).volume] := by
      simp_rw [← Finset.sum_add_distrib, ← left_distrib]
      congr with y
      by_cases hf : f y = 0
      . simp only [hf, zero_mul]
      congr 1
      convert multiDist_chainRule π (hΩc y) hX _
      refine h_indep.cond hY ?_ fun _ ↦ .singleton _
      apply prob_nonzero_of_prod_prob_nonzero
      convert hf
      rw [← ENNReal.toReal_prod]
      congr
      exact (iIndepFun.meas_iInter h_indep fun _ ↦ mes_of_comap <| .singleton _).symm
    _ = _ := by
      have hmes : Measurable (π ∘ ∑ i : Fin m, X i) := by
        apply Measurable.comp .of_discrete
        convert Finset.measurable_sum (f := X) Finset.univ _ with ω
        . exact Fintype.sum_apply ω X
        exact (fun i _ ↦ hX i)
      have hpi_indep : iIndepFun (fun i ↦ ⟨π ∘ X i, Y i⟩) ℙ := by
        set g : G × S → H × S := fun p ↦ ⟨π p.1, p.2⟩
        convert iIndepFun.comp h_indep (fun _ ↦ g) _
        intro i
        exact .of_discrete
      have hpi_indep' : iIndepFun (fun i ↦ ⟨X i, ⟨π ∘ X i, Y i⟩⟩) ℙ := by
        set g : G × S → G × (H × S) := fun p ↦ ⟨p.1, ⟨π p.1, p.2⟩⟩
        convert iIndepFun.comp h_indep (fun _ ↦ g) _
        intro i
        exact .of_discrete

      have hey_mes : ∀ y, MeasurableSet (E' y) := by
          intro y
          apply MeasurableSet.iInter
          intro i
          exact MeasurableSet.preimage (.singleton (y i)) (hY i)

      congr 2
      . rw [condMultiDist_eq' hX _ hpi_indep']
        . rw [← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow _ _ _).symm, Fintype.sum_prod_type, Finset.sum_comm]
          congr with y
          by_cases pey : ℙ (E' y) = 0
          . simp only [pey, ENNReal.toReal_zero, zero_mul, f]
            apply (Finset.sum_eq_zero _).symm
            intro s _
            convert zero_mul _
            convert ENNReal.toReal_zero
            apply measure_mono_null _ pey
            intro ω hω
            simp [E', Equiv.arrowProdEquivProdArrow] at hω ⊢
            intro i
            exact (hω i).2
          rw [condMultiDist_eq' (hΩ := hΩc y) hX, Finset.mul_sum]
          . congr with s
            dsimp [f, E', Equiv.arrowProdEquivProdArrow]
            rw [← mul_assoc, ← ENNReal.toReal_mul]
            congr 2
            . rw [mul_comm]
              convert cond_mul_eq_inter (hey_mes y) ?_ _
              . rw [← Set.iInter_inter_distrib]
                apply Set.iInter_congr
                intro i
                ext ω
                simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, comp_apply, Set.mem_inter_iff]
                exact And.comm
              infer_instance
            funext _
            congr 1
            dsimp [hΩc, E']
            rw [cond_cond_eq_cond_inter (hey_mes y), ← Set.iInter_inter_distrib]
            . congr 1
              apply Set.iInter_congr
              intro i
              ext ω
              simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, comp_apply, Prod.mk.injEq]
              exact And.comm
            apply MeasurableSet.iInter
            intro i
            apply MeasurableSet.preimage (.singleton _)
            exact Measurable.comp .of_discrete (hX i)
          . intro i
            exact Measurable.comp .of_discrete (hX i)
          set g : G → G × H := fun x ↦ ⟨x, π x⟩
          refine iIndepFun.comp ?_ (fun _ ↦ g) fun _ ↦ .of_discrete
          . refine h_indep.cond hY ?_ fun _ ↦ .singleton _
            rw [iIndepFun.meas_iInter h_indep fun _ ↦ mes_of_comap <| .singleton _] at pey
            contrapose! pey
            obtain ⟨i, hi⟩ := pey
            exact Finset.prod_eq_zero (Finset.mem_univ i) hi
        intro i
        exact Measurable.prodMk (.comp .of_discrete (hX i)) (hY i)
      . rw [condMultiDist_eq' _ hY hpi_indep]
        intro i
        apply Measurable.comp .of_discrete (hX i)
      rw [condMutualInfo_eq_sum', Fintype.sum_prod_type, Finset.sum_comm]
      . congr with y
        by_cases pey : ℙ (E' y) = 0
        . simp only [pey, ENNReal.toReal_zero, zero_mul, f]
          apply (Finset.sum_eq_zero _).symm
          intro s _
          convert zero_mul _
          simp [measureReal_eq_zero_iff]
          apply measure_mono_null _ pey
          intro ω hω
          simp [E'] at hω ⊢
          rw [← hω.2]
          simp only [implies_true]
        have : IsProbabilityMeasure (hΩc y).volume := cond_isProbabilityMeasure pey
        rw [condMutualInfo_eq_sum' hmes, Finset.mul_sum]
        congr with x
        dsimp [f, E']
        rw [← mul_assoc, measureReal_def, ← ENNReal.toReal_mul]
        congr 2
        . rw [mul_comm]
          convert cond_mul_eq_inter (hey_mes y) ?_ _
          . ext ω
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, comp_apply,
              Finset.sum_apply, _root_.map_sum, Set.mem_inter_iff, Set.mem_iInter, E']
            rw [and_comm]
            apply and_congr_left
            intro _
            exact funext_iff
          infer_instance
        dsimp [hΩc, E']
        rw [cond_cond_eq_cond_inter (hey_mes y)]
        . congr
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
            comp_apply, Finset.sum_apply, _root_.map_sum, Prod.mk.injEq, E']
          rw [and_comm]
          apply and_congr_right
          intro _
          exact Iff.symm funext_iff
        exact MeasurableSet.preimage (.singleton x) hmes
      exact Measurable.prodMk hmes (measurable_pi_lambda (fun ω i ↦ Y i ω) hY)


/-- Let `m` be a positive integer. Suppose one has a sequence `G_m → G_{m - 1} → ... → G_1 → G_0 = {0}`
of homomorphisms between abelian groups `G_0, ...,G_m`, and for each `d=0, ...,m`, let
`π_d : G_m → G_d` be the homomorphism from `G_m` to `G_d` arising from this sequence by composition
(so for instance `π_m` is the identity homomorphism and `π_0` is the zero homomorphism).
Let `X_[m] = (X_1, ..., X_m)` be a jointly independent tuple of `G_m`-valued random variables.
Then `D[X_[m]] = ∑ d, D[π_d(X_[m]) ,| , π_(d-1)(X_[m])]`
` + ∑_{d=1}^{m - 1}, I[∑ i, X_i : π_d(X_[m]) | π_d(∑ i, X_i), π_(d-1})(X_[m])]`.-/
lemma iter_multiDist_chainRule {m : ℕ}
    {G : Fin (m + 1) → Type*}
    [hG : ∀ i, MeasurableSpace (G i)] [hGs : ∀ i, MeasurableSingletonClass (G i)]
    [∀ i, AddCommGroup (G i)] [hGcount : ∀ i, Fintype (G i)]
    {φ : ∀ i : Fin m, G (i.succ) →+ G i.castSucc} {π : ∀ d, G ⊤ →+ G d}
    (hcomp: ∀ i : Fin m, π i.castSucc = (φ i) ∘ (π i.succ))
    {Ω : Type*} [hΩ : MeasureSpace Ω] {X : Fin m → Ω → G ⊤}
    (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X) (n : Fin (m + 1)) :
    D[X | fun i ↦ (π 0) ∘ X i; fun _ ↦ hΩ] = D[X | fun i ↦ (π n) ∘ X i; fun _ ↦ hΩ]
      + ∑ d ∈ Finset.Iio n, (D[fun i ↦ (π (d+1)) ∘ X i | fun i ↦ (π d) ∘ X i; fun _ ↦ hΩ]
      + I[∑ i, X i : fun ω ↦ (fun i ↦ (π (d+1)) (X i ω)) |
            ⟨(π (d+1)) ∘ ∑ i, X i, fun ω ↦ (fun i ↦ (π d) (X i ω))⟩]) := by
  set S := ∑ i, X i
  set motive := fun n:Fin (m + 1) ↦ D[X | fun i ↦ (π 0) ∘ X i; fun _ ↦ hΩ]
    = D[X | fun i ↦ (π n) ∘ X i; fun _ ↦ hΩ]
      + ∑ d ∈ Finset.Iio n, (D[fun i ↦ (π (d+1)) ∘ X i | fun i ↦ (π d) ∘ X i; fun _ ↦ hΩ]
      + I[S : fun ω ↦ (fun i ↦ (π (d+1)) (X i ω)) |
            ⟨(π (d+1)) ∘ S, fun ω ↦ (fun i ↦ (π d) (X i ω))⟩])
  have zero : motive 0 := by
    have : (Finset.Iio 0 : Finset (Fin (m + 1))) = ∅ := rfl
    simp [motive, this]
  have succ : (n : Fin m) → motive n.castSucc → motive n.succ := by
    intro n hn
    dsimp [motive] at hn ⊢
    have h2 : n.castSucc ∈ Finset.Iio n.succ := by simp [Fin.castSucc_lt_succ_iff]
    rw [hn, ← Finset.add_sum_erase _ _ h2, Iio_of_succ_eq_Iic_of_castSucc, Finset.Iic_erase,
      ← add_assoc, ← add_assoc, Fin.coeSucc_eq_succ]
    congr 1
    convert cond_multiDist_chainRule (X := X) (Y := fun i ↦ ⇑(π n.castSucc) ∘ X i) (π n.succ) hX ?_ ?_
    . set g : G n.succ → G n.succ × G n.castSucc := fun x ↦ ⟨x, ⇑(φ n) x⟩
      convert (condMultiDist_of_inj (f := g) (fun _ ↦ hΩ) X (fun i ↦ ⇑(π n.succ) ∘ X i) _).symm using 3 with i
      . ext ω
        . dsimp [g, prod]
        rw [hcomp n]
        simp [g]
      intro x x' h
      simp [g] at h
      exact h.1
    . intro _
      exact Measurable.comp .of_discrete (hX _)
    set g : G ⊤ → G ⊤ × G n.castSucc := fun x ↦ ⟨x, π n.castSucc x⟩
    convert iIndepFun.comp h_indep (fun _ ↦ g) _
    intro _
    exact .of_discrete
  exact Fin.induction zero succ n

/--Under the preceding hypotheses,
`D[X_[m]] ≥ ∑ d, D[π_d(X_[m])| π_(d-1})(X_[m])] + I[∑ i, X_i : π_1(X_[m]) | π_1(∑ i, X_i)]`. -/
lemma iter_multiDist_chainRule' {m : ℕ} (hm : m > 0)
    {G : Fin (m + 1) → Type*} [hG : ∀ i, MeasurableSpace (G i)]
    [hGs : ∀ i, MeasurableSingletonClass (G i)] [hGa : ∀ i, AddCommGroup (G i)]
    [hGcount : ∀ i, Fintype (G i)] {φ : ∀ i : Fin m, G (i.succ) →+ G i.castSucc}
    {π : ∀ d, G ⊤ →+ G d} (hπ0 : π 0 = 0) (hcomp : ∀ i : Fin m, π i.castSucc = φ i ∘ π i.succ)
    {Ω : Type*} [hΩ : MeasureSpace Ω] {X : Fin m → Ω → G ⊤}
    (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X) :
    D[X; fun _ ↦ hΩ] ≥
      ∑ d : Fin m, D[fun i ↦ π d.succ ∘ X i | fun i ↦ π d.castSucc ∘ X i; fun _ ↦ hΩ]
      + I[∑ i : Fin m, X i : fun ω i ↦ π 1 (X i ω)| π 1 ∘ ∑ i : Fin m, X i] := by
  have : IsProbabilityMeasure (ℙ : Measure Ω) := h_indep.isProbabilityMeasure
  calc
  _ = D[X | fun i ↦ π 0 ∘ X i ; fun _x ↦ hΩ] := by
    rw [hπ0]
    convert (condMultiDist_of_const (fun _ ↦ (0: G 0)) X).symm
  _ = D[X | fun i ↦ π ⊤ ∘ X i ; fun _ ↦ hΩ] +
    ∑ d ∈ .Iio (.last m),
      (D[fun i ↦ π (d + 1) ∘ X i | fun i ↦ π d ∘ X i ; fun _ ↦ hΩ] +
        I[∑ i : Fin m, X i : fun ω i ↦ (π (d + 1)) (X i ω)|⟨⇑(π (d + 1)) ∘ ∑ i : Fin m, X i, fun ω i ↦ (π d) (X i ω)⟩]) :=
    iter_multiDist_chainRule hcomp hX h_indep (.last m : Fin (m + 1))
  _ ≥ ∑ d ∈ .Iio (.last m),
      (D[fun i ↦ π (d + 1) ∘ X i | fun i ↦ π d ∘ X i ; fun _ ↦ hΩ] +
        I[∑ i : Fin m, X i : fun ω i ↦ (π (d + 1)) (X i ω)|⟨⇑(π (d + 1)) ∘ ∑ i : Fin m, X i, fun ω i ↦ (π d) (X i ω)⟩]) := by
      apply le_add_of_nonneg_left (condMultiDist_nonneg _ (fun _ => this) X _ hX)
  _ = ∑ d : Fin m,
      (D[fun i ↦ π d.succ ∘ X i | fun i ↦ π d.castSucc ∘ X i ; fun _ ↦ hΩ] +
        I[∑ i : Fin m, X i : fun ω i ↦ π d.succ (X i ω)|
          ⟨π d.succ ∘ ∑ i : Fin m, X i, fun ω i ↦ π d.castSucc (X i ω)⟩]) := by
      rw [← Fin.sum_univ_castSucc']
      congr! <;> rw [Fin.coeSucc_eq_succ]
  _ ≥ _ := by
      rw [Finset.sum_add_distrib]
      gcongr
      have : NeZero m := ⟨hm.ne'⟩
      let f (i : Fin m) :=
        I[∑ i', X i' : fun ω i' ↦ π i.succ (X i' ω)|
          ⟨π i.succ ∘ ∑ i', X i', fun ω i' ↦ π i.castSucc (X i' ω)⟩]
      have hf i : 0 ≤ f i := condMutualInfo_nonneg (by fun_prop) (by fun_prop)
      let F (x : G 1) : G 1 × (Fin m → G 0) := (x, fun _ ↦ 0)
      calc
        I[∑ i, X i : fun ω i ↦ π 1 (X i ω) | π 1 ∘ ∑ i, X i]
          = I[∑ i, X i : fun ω i ↦ π 1 (X i ω) | F ∘ π 1 ∘ ∑ i, X i] := by
          have hF : Injective F := fun x y ↦ congr_arg Prod.fst
          exact (condMutualInfo_of_inj (by fun_prop) (by fun_prop) (by fun_prop) _ hF).symm
        _ = f 0 := ?_
        _ ≤ ∑ j, f j := Finset.single_le_sum (f := f) (fun _ _ ↦ hf _) (Finset.mem_univ _)
      simp [f, hπ0, AddMonoidHom.zero_apply, F]
      rw [← Fin.succ_zero_eq_one']
      congr 1

theorem multiDist_of_hom' {G G': Type*}
  [MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G] [Fintype G]
  [MeasurableSpace G'] [MeasurableSingletonClass G'] [AddCommGroup G'] [Fintype G']
  {ι : G →+ G'} (hι: Function.Injective ⇑ι) {m:ℕ}
  {Ω : Fin m → Type*} (hΩ : (i:Fin m) → MeasureSpace (Ω i)) [∀ i, IsProbabilityMeasure (ℙ:Measure (Ω i))]
  {X : (i:Fin m) → (Ω i) → G} (hX : ∀ i, Measurable (X i)) (a: Fin m → G')
  : D[fun i ω ↦ ι (X i ω) + a i; hΩ] = D[X; hΩ] := by
  unfold multiDist
  congr 1
  . unfold entropy
    set sum_G : (Fin m → G) → G := fun x ↦ ∑ i, x i
    set sum_G' : (Fin m → G') → G' := fun x ↦ ∑ i, x i
    let ι' : G → G' := fun x ↦ ι x + ∑ i, a i
    have hι' : Function.Injective ι' := by intro x y hxy; simp [ι'] at hxy; exact hι hxy
    convert measureEntropy_map_of_injective _ ι' _ hι' <;> try fun_prop
    rw [Measure.map_map] <;> try fun_prop
    have : ι' ∘ sum_G = sum_G' ∘ (fun x i ↦ ι (x i) + a i) := by
      ext x; simp [ι', sum_G, sum_G', Finset.sum_add_distrib]
    rw [this, ←Measure.map_map] <;> try fun_prop
    congr
    convert (Measure.map_of_pi (f := fun i x ↦ ι x + a i) _ _).symm with i
    . rw [Measure.map_map] <;> try fun_prop
      congr
    . intro i; exact isProbabilityMeasure_map (by fun_prop)
    intro i; fun_prop
  congr 2; ext i
  apply entropy_comp_of_injective _ (hX i) (fun x ↦ ι x + a i) _
  intro x y hxy; simp at hxy; exact hι hxy

theorem multiDist_of_hom {G G': Type*}
  [MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G] [Fintype G]
  [MeasurableSpace G'] [MeasurableSingletonClass G'] [AddCommGroup G'] [Fintype G']
  {ι : G →+ G'} (hι: Function.Injective ⇑ι)
  {Ω : Type*} (hΩ : MeasureSpace Ω) [IsProbabilityMeasure (ℙ:Measure Ω)]
  {m:ℕ} {X : Fin m → Ω → G} (hX : ∀ i, Measurable (X i))
  : D[fun i ω ↦ ι (X i ω); fun _ ↦ hΩ] = D[X; fun _ ↦ hΩ] := by
  convert multiDist_of_hom' hι (fun _ ↦ hΩ) hX (fun _ ↦ 0); simp

theorem multiDist_congr {G:Type*} [MeasurableSpace G] [AddCommGroup G]
    {m : ℕ} {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i))
    {X X' : ∀ i, (Ω i) → G} (hae : ∀ i, X i =ᵐ[ℙ] X' i) : D[X; hΩ] = D[X'; hΩ] := by
    unfold multiDist
    congr 3 <;> ext1 i
    . apply MeasureTheory.Measure.map_congr (hae i)
    apply entropy_congr (hae i)

theorem condMultiDist_of_hom {G G' S: Type*} [Fintype S]
  [MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G] [Fintype G]
  [MeasurableSpace G'] [MeasurableSingletonClass G'] [AddCommGroup G'] [Fintype G']
  [MeasurableSpace S] [MeasurableSingletonClass S]
  {ι : G →+ G'} (hι: Function.Injective ⇑ι)
  {Ω : Type*} (hΩ : MeasureSpace Ω) [IsProbabilityMeasure (ℙ:Measure Ω)]
  {m:ℕ} {X : Fin m → Ω → G} (hX : ∀ i, Measurable (X i))
  {Y: Fin m → Ω → S} (hY : ∀ i, Measurable (Y i)) (a: Fin m → S → G')
  : D[fun i ω ↦ ι (X i ω) + a i (Y i ω) | Y; fun _ ↦ hΩ] = D[X | Y; fun _ ↦ hΩ] := by
  unfold condMultiDist
  apply Finset.sum_congr rfl; intro y _
  by_cases h: ∀ i, ℙ ( Y i ⁻¹' {y i} ) ≠ 0
  . congr; calc
      _ =  D[fun i ω ↦ ι (X i ω) + a i (y i) ; fun i ↦ ⟨ℙ[|Y i ⁻¹' {y i}]⟩]  := by
        convert multiDist_congr (fun i ↦ ⟨ℙ[|Y i ⁻¹' {y i}]⟩) _
        intro i
        convert Filter.EventuallyEq.comp₂ (f := fun ω ↦ Y i ω) (f' := fun ω ↦ y i) (g := id) (g' := id) _ (fun y' ω ↦ ι (X i ω) + a i y') ae_eq_rfl
        rw [Filter.EventuallyEq.eq_1]
        apply Filter.Eventually.mono (p := fun ω ↦ ω ∈ Y i ⁻¹' {y i})
        . apply ae_cond_mem; measurability
        intro ω; simp
      _ = _ := by
        convert multiDist_of_hom' hι (fun i ↦ ⟨ℙ[|Y i ⁻¹' {y i}]⟩) hX _
        intro i; exact cond_isProbabilityMeasure (h i)
  simp at h ⊢; right
  obtain ⟨i, hi⟩ := h; apply Finset.prod_eq_zero (i:= i) <;> simp [hi]

lemma cond_entropy_indep {Ω:Type*} [hΩ:MeasureSpace Ω] {S T U: Type*}
    {X: Ω → S} {Y: Ω → T} {Z: Ω → U}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U]
    (hX : Measurable X) (hY: Measurable Y) (hZ: Measurable Z)
    [IsZeroOrProbabilityMeasure hΩ.volume] (hindep : IndepFun (⟨X,Y⟩) Z):
    H[X | ⟨Y,Z⟩] = H[X | Y] := by
      have h1 : H[X | ⟨Y,Z⟩] = H[⟨X, ⟨Y,Z⟩⟩] - H[⟨Y,Z⟩] := chain_rule'' _ (by fun_prop) (by fun_prop)
      have h2 : H[X | Y] = H[⟨X,Y⟩] - H[Y] := chain_rule'' _ (by fun_prop) (by fun_prop)
      have h3 : H[⟨X, ⟨Y,Z⟩⟩] = H[⟨⟨X,Y⟩,Z⟩] :=
        entropy_of_comp_eq_of_comp _ (by fun_prop) (by fun_prop)
        (fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩) (fun x ↦ ⟨x.1.1, ⟨x.1.2, x.2⟩⟩) (by rfl) (by rfl)
      have h4 : H[⟨⟨X,Y⟩,Z⟩] = H[⟨X,Y⟩] + H[Z] := IndepFun.entropy_pair_eq_add (by fun_prop) (by fun_prop) hindep
      have h5 : H[⟨Y,Z⟩] = H[Y] + H[Z] := by
        apply IndepFun.entropy_pair_eq_add <;> try fun_prop
        convert IndepFun.comp (φ := fun x ↦ x.2) (ψ := id) hindep _ _ <;> try fun_prop
      linarith

set_option maxHeartbeats 300000 in
/-- Let `G` be an abelian group and let `m ≥ 2`. Suppose that `X_{i,j}`, `1 ≤ i, j ≤ m`, are
independent `G`-valued random variables. Then
`I[(∑ i, X_{i,j})_{j=1}^m : (∑ j, X_{i,j})_{i=1}^m | ∑ i j, X_{i,j}]`
is less than
`∑_{j=1}^{m - 1} (D[(X_{i, j})_{i=1}^m] - D[(X_{i, j})_{i = 1}^m | (X_{i,j} + ... + X_{i,m})_{i=1}^m])`
`+ D[(X_{i,m})_{i=1}^m] - D[(∑ j, X_{i,j})_{i=1}^m],`
where all the multidistances here involve the indexing set `{1, ..., m}`. -/
lemma cor_multiDist_chainRule [Fintype G] {m : ℕ} {Ω : Type*} (hΩ : MeasureSpace Ω)
    (X : Fin (m + 1) × Fin (m + 1) → Ω → G) (hmes : ∀ i, Measurable (X i)) (h_indep : iIndepFun X)
    [IsProbabilityMeasure (ℙ:Measure Ω)]:
    I[fun ω ↦ (fun j ↦ ∑ i, X ⟨i, j⟩ ω) : fun ω ↦ (fun i ↦ ∑ j, X ⟨i, j⟩ ω) | ∑ p, X p]
      ≤ ∑ j : Fin m, (D[fun i ↦ X ⟨i, j.castSucc⟩; fun _ ↦ hΩ] - D[fun i ↦ X ⟨i, j.castSucc⟩ |
        fun i ↦ ∑ k ∈ Finset.Ici j.castSucc, X ⟨i, k⟩; fun _ ↦ hΩ]) + D[fun i ↦ X ⟨i, ⊤⟩; fun _ ↦ hΩ]
         - D[fun i ↦ ∑ j, X ⟨i, j⟩; fun _ ↦ hΩ] := by
  let G' : Fin (m + 2) → Type uG := fun i ↦ (Fin i → G)
  let φ₀ (i : Fin (m + 1)) (x : G' i.succ) (j: Fin i) : G := if j.val+1 = i then
          x ⟨i.val-1, by simp; omega⟩ + x ⟨i.val, by simp⟩
        else
          x ⟨j, by have := j.isLt; simp only [Fin.val_succ] at this ⊢; omega⟩
  let φ (i : Fin (m + 1)) : G' i.succ →+ G' i.castSucc := {
      toFun x j := φ₀ i x j
      map_add' x y :=  by ext ⟨j, hj⟩; by_cases hj' : j + 1 = i <;> simp [hj', φ₀, G']; abel
      map_zero' := by ext; simp [G', φ₀]
    }
  let π₀ (d : Fin (m + 2)) (x : G' ⊤) (i: Fin d) : G := if i.val+1 = d then
          (∑ j ∈ Finset.Ici ⟨d.val-1, by have := d.isLt; simp; omega⟩, x j)
        else
          x ⟨i, by have := i.isLt; simp; omega⟩
  let π (d : Fin (m + 2)) : G' ⊤ →+ G' d := {
      toFun x i := π₀ d x i
      map_add' x y := by ext i; by_cases hi : i.val + 1 = d <;> simp [hi, π₀, G']; simp [←Finset.sum_add_distrib]
      map_zero' := by ext; simp [G', π₀]
    }
  have hπ0: π 0 = 0 := by ext _ _ z; exact Fin.elim0 z
  have hcomp (i:Fin (m + 1)) : π i.castSucc = φ i ∘ π i.succ := by
    obtain ⟨i, hi⟩ := i; ext x ⟨j, hj⟩
    by_cases h: j + 1 = i <;> simp [h, φ₀, π₀,π, φ]
    . simp [(show ¬ i-1 = i by omega)]
      convert (Finset.add_sum_erase _ x _).symm using 3
      . ext ⟨k, hk⟩; simp at h ⊢; omega
      simp
    intro h'
    convert (Finset.sum_singleton x ⟨i,hi⟩).symm using 2
    . simp [h']
    ext ⟨k, hk⟩; simp at hj ⊢; omega
  let X' : Fin (m + 1) → Ω → G' ⊤ := fun i ω j ↦ X (i, j) ω
  have h_indep': iIndepFun X' := by
    let S : Fin (m + 1) → Finset (Fin (m + 1) × Fin (m + 1)) := fun i ↦ {p | p.1 = i}
    let φ : (j:Fin (m + 1)) → ((i: S j) → G) → G' ⊤ := fun j x k ↦ x ⟨(j, k), by simp [S]⟩
    apply h_indep.finsets_comp S _ hmes φ (by fun_prop)
    rw [Finset.pairwiseDisjoint_iff]
    rintro _ _ _ _ ⟨⟨_, _⟩, hij⟩
    simp [S] at hij
    omega
  have h1 := iter_multiDist_chainRule' (by linarith) hπ0 hcomp (by fun_prop) h_indep'
  have h2 :  D[X' ; fun _ ↦ hΩ] = D[fun i ↦ X (i, ⊤) ; fun x ↦ hΩ] + ∑ j : Fin m, D[fun i ↦ X ⟨i, j.castSucc⟩; fun _ ↦ hΩ] := calc
    _ = ∑ j, H[∑ i, X ⟨i, j⟩ ] - (∑ i, ∑ j, H[X ⟨i, j⟩]) / ↑(m + 1) := by
      rw [multiDist_indep _ (by fun_prop) h_indep']
      congr
      . convert iIndepFun.entropy_eq_add _ _ with i _ ω <;> try infer_instance
        . simp [X']
        . fun_prop
        simp [X']
        let S : Fin (m + 1) → Finset (Fin (m + 1) × Fin (m + 1)) := fun i ↦ {p | p.2 = i}
        let φ : (i:Fin (m + 1)) → ((_: S i) → G) → G := fun i x ↦ ∑ j, x ⟨(j,i), by simp [S]⟩
        apply h_indep.finsets_comp S _ hmes φ (by fun_prop)
        rw [Finset.pairwiseDisjoint_iff]
        rintro _ _ _ _ ⟨⟨_, _⟩, hij⟩
        simp [S] at hij
        omega
      ext i
      convert iIndepFun.entropy_eq_add _ _ <;> try infer_instance
      . fun_prop
      simp
      let S : Fin (m + 1) → Finset (Fin (m + 1) × Fin (m + 1)) := fun j ↦ {(i,j)}
      let φ : (j:Fin (m + 1)) → ((_: S j) → G) → G := fun j x ↦ x ⟨(i,j), by simp [S]⟩
      apply h_indep.finsets_comp S _ hmes φ (by fun_prop)
      rw [Finset.pairwiseDisjoint_iff]
      rintro _ _ _ _ ⟨⟨_, _⟩, hij⟩
      simp [S] at hij
      omega
    _ = ∑ j, (H[∑ i, X ⟨i, j⟩ ] - (∑ i, H[X ⟨i, j⟩]) / ↑(m + 1)) := by
      rw [Finset.sum_sub_distrib, ←Finset.sum_div, Finset.sum_comm]
    _ = ∑ j, D[fun i ↦ X ⟨i, j⟩; fun _ ↦ hΩ] := by
      apply Finset.sum_congr rfl; intro j _
      symm; apply multiDist_indep <;> try fun_prop
      let S : Fin (m + 1) → Finset (Fin (m + 1) × Fin (m + 1)) := fun i ↦ {(i,j)}
      let φ : (i:Fin (m + 1)) → ((_: S i) → G) → G := fun i x ↦ x ⟨(i,j), by simp [S]⟩
      apply h_indep.finsets_comp S _ hmes φ (by fun_prop)
      rw [Finset.pairwiseDisjoint_iff]
      rintro _ _ _ _ ⟨⟨_, _⟩, hij⟩
      simp [S] at hij
      omega
    _ = D[fun i ↦ X (i, ⊤) ; fun x ↦ hΩ] + ∑ j ∈ .Iio (.last _), D[fun i ↦ X ⟨i, j⟩; fun _ ↦ hΩ] := by
      convert (Finset.add_sum_erase _ _ _).symm using 3
      . ext ⟨j, hj⟩; simp [Fin.last, Top.top]; omega
      . infer_instance
      simp
    _ = _ := by
      congr 1
      convert Finset.sum_map _ Fin.castSuccOrderEmb.toEmbedding _
      ext ⟨j, hj⟩; simp
  have h3 : ∑ j : Fin (m + 1), D[fun i ↦ ⇑(π j.succ) ∘ X' i | fun i ↦ ⇑(π j.castSucc) ∘ X' i ; fun x ↦ hΩ]
    = D[fun i ↦ ∑ j, X ⟨i, j⟩ ; fun x ↦ hΩ] + ∑ j : Fin m, D[fun i ↦ X ⟨i, j.castSucc⟩ | fun i ↦ ∑ k ∈ Finset.Ici j.castSucc, X ⟨i, k⟩ ; fun x ↦ hΩ] := calc
    _ = D[fun i ↦ ∑ j, X ⟨i, j⟩ ; fun x ↦ hΩ] + ∑ j ∈ (Finset.univ.erase 0 : Finset (Fin (m + 1))), D[fun i ↦ ⇑(π j.succ) ∘ X' i | fun i ↦ ⇑(π j.castSucc) ∘ X' i ; fun x ↦ hΩ] := by
      convert (Finset.add_sum_erase _ _ _).symm using 2
      . trans D[fun i ↦ ⇑(π (0:Fin (m + 1)).succ) ∘ X' i; fun x ↦ hΩ]
        . let ι' : G →+ G' (.succ 0) := {
             toFun x _ := x
             map_zero' := rfl
             map_add' x y := rfl
            }
          have : Function.Injective ⇑ι' := by
            intro x y hxy; simp [ι'] at hxy
            exact congr($hxy ⟨0, by simp⟩)
          convert (multiDist_of_hom this hΩ _).symm with i ω
          . ext j; simp [π, π₀, X',G',Finset.sum_apply]
            apply Finset.sum_congr
            . ext i; simp
            intros; rfl
          fun_prop
        convert (condMultiDist_of_const (fun _ ↦ Fin.elim0) _).symm with i ω <;> try infer_instance
        ext ⟨j, hj⟩; simp at hj
      simp
    _ = D[fun i ↦ ∑ j, X ⟨i, j⟩ ; fun x ↦ hΩ] + ∑ j : Fin m, D[fun i ↦ ⇑(π j.succ.succ) ∘ X' i | fun i ↦ ⇑(π j.succ.castSucc) ∘ X' i ; fun x ↦ hΩ] := by
      congr 1
      convert Finset.sum_map _ (Fin.succEmb _) _
      ext ⟨j, hj⟩; simp
    _ = _ := by
      congr; ext j
      calc
        _ = D[fun i ↦ X (i, j.castSucc) | fun i ↦ ⇑(π j.succ.castSucc) ∘ X' i ; fun x ↦ hΩ] := by
          let ι' : G →+ G' (j.succ.succ) := {
            toFun x k := if k.val = j+1 then (-x) else if k.val = j then x else 0
            map_zero' := by ext k; by_cases h:k.val = j+1 <;> by_cases h':k.val = j <;> simp [h,h',G']
            map_add' x y := by
              ext k; by_cases h:k.val = j+1 <;> by_cases h':k.val = j <;> simp [h,h',G'] <;> abel
          }
          have : Function.Injective ⇑ι' := by
            intro x y hxy; replace hxy := congrFun hxy ⟨j.val, by simp; omega⟩
            simpa [ι'] using hxy
          let a : Fin (m + 1) → G' j.succ.castSucc → G' (j.succ.succ) := fun i x k ↦ if h:k.val = j+1 then x (Fin.last _) else if h':k.val = j then 0 else x ⟨k, by obtain ⟨k, hk⟩ := k; simp at hk h h' ⊢; omega⟩
          convert condMultiDist_of_hom this hΩ _ _ a with i ω
          . ext k
            by_cases h:k.val = j+1 <;> by_cases h':k.val = j <;> simp [G', π, π₀, X', ι', a, h, h']
            . omega
            . rw [eq_neg_add_iff_add_eq, add_comm]
              convert Finset.sum_erase_add (a := j.castSucc) _ _ _ using 3
              . ext ⟨l, hl⟩; obtain ⟨j, hj⟩ := j; simp; omega
              obtain ⟨j, hj⟩ := j; simp
            congr
          all_goals intros; fun_prop
        _ = _ := by
          let S : Fin (m + 1) → Finset (Fin (m + 1) × Fin (m + 1)) := fun i ↦ {p | p.1 = i}
          have h_disjoint : Set.PairwiseDisjoint .univ S := by
            rw [Finset.pairwiseDisjoint_iff]
            rintro _ _ _ _ ⟨⟨_, _⟩, hij⟩
            simp [S] at hij
            grind
          rw [condMultiDist_eq, condMultiDist_eq] <;> try intros; fun_prop
          . congr 1
            . let f : (Fin (m + 1) → G' j.succ.castSucc) → ((Fin (m + 1) → G) × (Fin (m + 1) → Fin j.val → G)) := fun x ↦ ⟨fun i ↦ x i ⟨j, by simp⟩, fun i ⟨k, hk⟩ ↦ x i ⟨k, by simp; omega⟩⟩
              have hf : Function.Injective f := by
                intro x y hxy; simp [f] at hxy
                ext i ⟨k, hk⟩; simp at hk
                by_cases hk' : k = j
                . convert congrFun hxy.1 i
                convert congrFun (congrFun hxy.2 i) ⟨k, by omega⟩
              rw [←condEntropy_of_injective' _ _ _ _ hf _] <;> try fun_prop
              convert cond_entropy_indep
                (Z := fun ω i (k:Fin j) ↦ X (i, ⟨k, by obtain ⟨j,hj⟩ := j; obtain ⟨k, hk⟩ := k; simp at hk ⊢; omega⟩) ω)
                _ _ _ _ with ω i k ω i <;> try infer_instance
              all_goals try fun_prop
              . obtain ⟨k, hk⟩ := k
                simp [f, π, X', π₀, (show ¬ k = j by omega)]
              . simp [f, π, X', π₀]; congr
              set T : Finset (Fin (m + 1) × Fin (m + 1)) := { p | p.2.val ≥ j }
              set T' : Finset (Fin (m + 1) × Fin (m + 1)) := { p | p.2.val < j }
              have h_disjoint : Disjoint T T' := by
                rw [Finset.disjoint_iff_ne]
                intro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂
                by_contra! h
                simp [T, T'] at h₁ h₂ h
                rw [h.2] at h₁
                order
              let φ : (T → G) → G × (Fin (m + 1) → G) := fun x ↦ ⟨∑ i, x ⟨(i, j.castSucc), by simp [T]⟩, fun i ↦ ∑ k : Finset.Ici j.castSucc, x ⟨⟨i, k⟩, by obtain ⟨k,hk⟩ := k; simpa [T] using hk⟩⟩
              let φ' : (T' → G) → (Fin (m + 1) → Fin j → G) := fun x i k ↦ x ⟨(i, k.castLE (by obtain ⟨j, hj⟩ := j; simp; omega)), by obtain ⟨k, hk⟩ := k; simpa [T'] using hk⟩
              convert h_indep.finsets_comp' h_disjoint hmes (show Measurable φ by fun_prop) (show Measurable φ' by fun_prop) using 1
              ext ω i <;> simp [π, φ, f, π₀, X']
              convert (Finset.sum_attach _ _).symm using 1
            congr 2; ext i
            let f : (G' j.succ.castSucc) → (G × (Fin j → G)) := fun x ↦ ⟨x ⟨j, by simp⟩, fun ⟨k, hk⟩ ↦ x ⟨k, by simp; omega⟩⟩
            have hf : Function.Injective f := by
              intro x y hxy; simp [f] at hxy
              ext ⟨k, hk⟩; simp at hk
              by_cases hk' : k = j
              . convert hxy.1
              convert congrFun hxy.2 ⟨k, by omega⟩
            rw [←condEntropy_of_injective' _ _ _ _ hf _] <;> try fun_prop
            convert cond_entropy_indep
              (Z := fun ω (k:Fin j) ↦ X (i, ⟨k, by obtain ⟨j,hj⟩ := j; obtain ⟨k, hk⟩ := k; simp at hk ⊢; omega⟩) ω)
              _ _ _ _ with ω k ω <;> try infer_instance
            all_goals try fun_prop
            . obtain ⟨k, hk⟩ := k
              simp [f, π, X', π₀, (show ¬ k = j by omega)]
            . simp [f, π, X', π₀]; congr
            let T : Finset (Fin (m + 1) × Fin (m + 1)) := {p | p.1 = i ∧ p.2.val ≥ j}
            let T' : Finset (Fin (m + 1) × Fin (m + 1)) := {p | p.1 = i ∧ p.2.val < j}
            have h_disjoint' : Disjoint T T' := by
              rw [Finset.disjoint_iff_ne]
              intro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂
              by_contra! h; simp [T, T'] at h₁ h₂ h
              rw [h.2] at h₁
              replace h₁ := h₁.2; replace h₂ := h₂.2; order
            let φ : (T → G) → G × G := fun x ↦ ⟨x ⟨(i, j.castSucc), by simp [T]⟩, ∑ k : Finset.Ici j.castSucc, x ⟨⟨i, k⟩, by obtain ⟨k,hk⟩ := k; simpa [T] using hk⟩⟩
            let φ' : (T' → G) → (Fin j.val → G) := fun x k ↦ x ⟨⟨i,k.castLE (by obtain ⟨j,hj⟩ := j; simp; omega)⟩, by obtain ⟨k, hk⟩ := k; simpa [T'] using hk⟩
            convert h_indep.finsets_comp' h_disjoint' hmes (show Measurable φ by fun_prop) (show Measurable φ' by fun_prop) using 1
            ext ω <;> simp [π, φ, f, π₀, X']
            convert (Finset.sum_attach _ _).symm using 1
          . let φ : (i:Fin (m + 1)) → ((_: S i) → G) → G × G := fun i x ↦ ⟨x ⟨(i,j.castSucc), by simp [S]⟩, ∑ k ∈ Finset.Ici j.castSucc, x ⟨(i, k), by simp [S]⟩⟩
            convert h_indep.finsets_comp S h_disjoint hmes φ (by fun_prop) with i ω; simp
          . let φ : (i:Fin (m + 1)) → ((_: S i) → G) → G × (G' j.succ.castSucc) := fun i x ↦ ⟨x ⟨(i,j.castSucc), by simp [S]⟩, π j.succ.castSucc (fun k ↦ x ⟨(i, k), by simp [S]⟩)⟩
            exact h_indep.finsets_comp S h_disjoint hmes φ (by fun_prop)
  have h4 : I[∑ i, X' i : fun ω i ↦ (π 1) (X' i ω)|⇑(π 1) ∘ ∑ i, X' i] = I[fun ω j ↦ ∑ i, X ⟨i, j⟩ ω : fun ω i ↦ ∑ j, X ⟨i, j⟩ ω|∑ p, X p] := by
    let f : (Fin (m + 1) → G) → (G' ⊤) := fun x ⟨i, hi⟩ ↦ x ⟨i, by simpa using hi⟩
    have hf : Function.Injective f := by intro x y hxy; simpa [f] using hxy
    let g : (Fin (m + 1) → G) → (Fin (m + 1) → G' 1) := fun x i j ↦ x i
    have hg : Function.Injective g := by intro x y hxy; ext i; simp [g] at hxy; exact congr($hxy i ⟨0, by simp⟩)
    let h : G → G' 1 := fun x j ↦ x
    have hh : Function.Injective h := by intro x y hxy; simp [h] at hxy; exact congr($hxy ⟨0, by simp⟩)
    convert condMutualInfo_of_inj' _ _ _ _ hf hg hh with ω i ω i <;> try infer_instance
    . ext _; simp [π, π₀, X', g]; apply Finset.sum_congr
      . ext j; simp
      intros; rfl
    . ext ω _; simp [π, π₀, X', h]
      convert (Finset.sum_product_right _ _ _).symm with i _ j _; rfl
      ext ⟨i, j⟩; simp
    . rw [←Finset.sum.eq_1, Finset.sum_apply, Finset.sum_apply]
    . rw [←Finset.sum.eq_1]; fun_prop
    all_goals fun_prop
  rw [Finset.sum_sub_distrib]
  linarith

end multiDistance_chainRule
