import PFR.ForMathlib.Entropy.RuzsaDist

/-!
# The fibring identity

The proof of the fibring identity, which is a key component of the proof of PFR.

## Main statement

* `sum_of_rdist_eq`: If $Y_1,Y_2,Y_3,Y_4$ are independent, then $d[Y_1; Y_2] + d[Y_3; Y_4]$ is equal to the sum of
$$d[Y_1+Y_3; Y_2+Y_4] + d[Y_1|Y_1+Y_3; Y_2|Y_2+Y_4] $$
and
$$ I[Y_1+Y_2 : Y_2 + Y_4 | Y_1+Y_2+Y_3+Y_4].$$

-/

open MeasureTheory ProbabilityTheory Function

section GeneralFibring

-- $\pi : H \to H'$ is a homomorphism between additive groups.
variable {H : Type*} [AddCommGroup H] [Countable H] [hH : MeasurableSpace H]
  [MeasurableSingletonClass H]
  {H' : Type*} [AddCommGroup H'] [Countable H'] [hH' : MeasurableSpace H']
  [MeasurableSingletonClass H']
  (π : H →+ H')
variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- If $Z_1, Z_2$ are independent, then $d[Z_1; Z_2]$ is equal to
$$ d[\pi(Z_1);\pi(Z_2)] + d[Z_1|\pi(Z_1); Z_2 |\pi(Z_2)]$$
plus
$$I( Z_1 - Z_2 : (\pi(Z_1), \pi(Z_2)) | \pi(Z_1 - Z_2) ).$$
-/
lemma rdist_of_indep_eq_sum_fibre {Z_1 Z_2 : Ω → H} (h : IndepFun Z_1 Z_2 μ)
    (h1 : Measurable Z_1) (h2 : Measurable Z_2) [FiniteRange Z_1] [FiniteRange Z_2]:
    d[Z_1; μ # Z_2; μ] = d[π ∘ Z_1; μ # π ∘ Z_2; μ] + d[Z_1|π∘Z_1; μ # Z_2|π∘Z_2; μ] + I[Z_1-Z_2 : ⟨π∘Z_1, π∘Z_2⟩ | π∘(Z_1 - Z_2); μ] := by
  have hπ : Measurable π := .of_discrete
  have step1 : d[Z_1; μ # Z_2; μ] = d[π ∘ Z_1; μ # π ∘ Z_2; μ] +
      H[(Z_1 - Z_2)| π ∘ (Z_1 - Z_2); μ] - H[Z_1 | π ∘ Z_1; μ] / 2 - H[Z_2 | π ∘ Z_2; μ] / 2 := by
    have hsub : H[(Z_1 - Z_2)| π ∘ (Z_1 - Z_2); μ] = H[(Z_1 - Z_2); μ] - H[π ∘ (Z_1 - Z_2); μ] :=
      condEntropy_comp_self (by fun_prop) hπ
    rw [h.rdist_eq h1 h2, (h.comp hπ hπ).rdist_eq (hπ.comp h1) (hπ.comp h2),
      condEntropy_comp_self h1 hπ, condEntropy_comp_self h2 hπ, hsub, map_comp_sub π]
    ring_nf
  have m0 : Measurable (fun x ↦ (x, π x)) := .of_discrete
  have h' : IndepFun (⟨Z_1, π ∘ Z_1⟩) (⟨Z_2, π ∘ Z_2⟩) μ := h.comp m0 m0
  have m1 : Measurable (Z_1 - Z_2) := h1.sub h2
  have m2 : Measurable (⟨↑π ∘ Z_1, ↑π ∘ Z_2⟩) := (hπ.comp h1).prod_mk (hπ.comp h2)
  have m3 : Measurable (↑π ∘ (Z_1 - Z_2)) := hπ.comp m1
  have entroplem : H[Z_1 - Z_2|⟨⟨↑π ∘ Z_1, ↑π ∘ Z_2⟩, ↑π ∘ (Z_1 - Z_2)⟩; μ]
      = H[Z_1 - Z_2|⟨↑π ∘ Z_1, ↑π ∘ Z_2⟩; μ] := by
    rw [map_comp_sub π]
    let f : H' × H' → (H' × H') × H' := fun (x,y) ↦ ((x,y), x - y)
    have hf : Injective f := fun _ _ h ↦ (Prod.ext_iff.1 h).1
    have mf : Measurable f := measurable_id.prod_mk measurable_sub
    refine condEntropy_of_injective' μ m1 m2 f hf (mf.comp m2)
  rw [step1, condMutualInfo_eq' m1 m2 m3, entroplem,
    condRuzsaDist_of_indep h1 (hπ.comp h1) h2 (hπ.comp h2) μ h']
  ring_nf

lemma rdist_le_sum_fibre {Z_1 : Ω → H} {Z_2 : Ω' → H}
  (h1 : Measurable Z_1) (h2 : Measurable Z_2) [FiniteRange Z_1] [FiniteRange Z_2] :
  d[π ∘ Z_1; μ # π ∘ Z_2; μ'] + d[Z_1|π∘Z_1; μ # Z_2|π∘Z_2; μ'] ≤ d[Z_1; μ # Z_2; μ']:= by
  obtain ⟨ν, W_1, W_2, hν, m1, m2, hi, hi1, hi2, _, _⟩ := ProbabilityTheory.independent_copies_finiteRange h1 h2 μ μ'
  have hπ : Measurable π := .of_discrete
  have hφ : Measurable (fun x ↦ (x, π x)) := .of_discrete
  have hπ1 : IdentDistrib (⟨Z_1, π ∘ Z_1⟩) (⟨W_1, π ∘ W_1⟩) μ ν := hi1.symm.comp hφ
  have hπ2 : IdentDistrib (⟨Z_2, π ∘ Z_2⟩) (⟨W_2, π ∘ W_2⟩) μ' ν := hi2.symm.comp hφ
  rw [← hi1.rdist_eq hi2, ← (hi1.comp hπ).rdist_eq (hi2.comp hπ),
    rdist_of_indep_eq_sum_fibre π hi m1 m2,
    condRuzsaDist_of_copy h1 (hπ.comp h1) h2 (hπ.comp h2) m1 (hπ.comp m1) m2 (hπ.comp m2) hπ1 hπ2]
  exact le_add_of_nonneg_right (condMutualInfo_nonneg (by fun_prop) (by fun_prop))

/-- \[d[X;Y]\geq d[\pi(X);\pi(Y)].\] -/
lemma rdist_of_hom_le {Z_1 : Ω → H} {Z_2 : Ω' → H}
    (h1 : Measurable Z_1) (h2 : Measurable Z_2) [FiniteRange Z_1] [FiniteRange Z_2] :
    d[π ∘ Z_1; μ # π ∘ Z_2; μ'] ≤ d[Z_1; μ # Z_2; μ'] := by
  apply le_trans _ (rdist_le_sum_fibre π h1 h2 (μ := μ) (μ' := μ'))
  rw [le_add_iff_nonneg_right]
  exact condRuzsaDist_nonneg h1 (by fun_prop) h2 (by fun_prop)

end GeneralFibring

variable {G : Type*} [AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The conditional Ruzsa Distance step of `sum_of_rdist_eq` -/
lemma sum_of_rdist_eq_step_condRuzsaDist {Y : Fin 4 → Ω → G} (h_indep : iIndepFun (fun _ : Fin 4 ↦ hG) Y μ)
  (h_meas : ∀ i, Measurable (Y i)) :
    d[⟨Y 0, Y 2⟩ | Y 0 - Y 2 ; μ # ⟨Y 1, Y 3⟩ | Y 1 - Y 3 ; μ] = d[Y 0 | Y 0 - Y 2 ; μ # Y 1 | Y 1 - Y 3 ; μ] := by
  let Y' : Fin 4 → Ω → G
    | 0 => Y 0
    | 1 => Y 1
    | 2 => Y 0 - Y 2
    | 3 => Y 1 - Y 3
  let f : (G × G) → (G × G) := fun (g, h) ↦ (g, g - h)
  have hf : Measurable f := .of_discrete
  have h_indep' : IndepFun (⟨Y' 0, Y' 2⟩) (⟨Y' 1, Y' 3⟩) μ :=
    (h_indep.indepFun_prod_mk_prod_mk h_meas 0 2 1 3
      (by decide) (by decide) (by decide) (by decide)).comp hf hf
  have h_meas' : ∀ i, Measurable (Y' i)
    | 0 => h_meas 0
    | 1 => h_meas 1
    | 2 => (h_meas 0).sub (h_meas 2)
    | 3 => (h_meas 1).sub (h_meas 3)
  have h' (i j : Fin 4) : ⟨Y i, Y j⟩ = ⟨Y i, Y i - (Y i - Y j)⟩ := by simp only [sub_sub_cancel]
  rw [h' 0 2, h' 1 3]
  exact condRuzsaDist_of_inj_map Y' h_indep' h_meas'
    ((AddMonoidHom.fst G G).prod ((AddMonoidHom.fst G G) - (AddMonoidHom.snd G G)))
    (fun _ _ _ h ↦ (Prod.ext_iff.1 h).1)

/-- The conditional mutual information step of `sum_of_rdist_eq` -/
lemma sum_of_rdist_eq_step_condMutualInfo {Y : Fin 4 → Ω → G}
  (h_meas : ∀ i, Measurable (Y i)) :
    I[⟨Y 0 - Y 1, Y 2 - Y 3⟩:⟨Y 0 - Y 2, Y 1 - Y 3⟩|Y 0 - Y 1 - (Y 2 - Y 3);μ] =
    I[Y 0 - Y 1 : Y 1 - Y 3|Y 0 - Y 1 - Y 2 + Y 3;μ] := by
  suffices I[⟨Y 0 - Y 1, Y 2 - Y 3⟩:⟨Y 0 - Y 2, Y 1 - Y 3⟩|Y 0 - Y 1 - (Y 2 - Y 3);μ] =
    I[Y 0 - Y 1 : Y 1 - Y 3|Y 0 - Y 1 - (Y 2 - Y 3) ; μ] by convert this using 2; abel
  symm
  have hm (f : G → G → G × G) {a b i j k l : Fin 4} :
    Measurable (uncurry f ∘ ⟨Y i - Y j - (Y k - Y l), Y a - Y b⟩) := by fun_prop
  have hmf : Measurable fun ω ↦ ((Y 0 - Y 1) ω, (Y 0 - Y 1) ω - (Y 0 - Y 1 - (Y 2 - Y 3)) ω) :=
    hm (fun z x ↦ (x, x - z))
  have hmg : Measurable fun ω ↦ ((Y 1 - Y 3) ω + (Y 0 - Y 1 - (Y 2 - Y 3)) ω, (Y 1 - Y 3) ω) :=
    hm (fun z x ↦ (x + z, x))
  have hmij {i j : Fin 4} : Measurable (Y i - Y j) := (h_meas _).sub (h_meas _)
  have hm0123 {i j k l : Fin 4} : Measurable (Y i - Y j - (Y k - Y l)) :=
    ((h_meas _).sub (h_meas _)).sub ((h_meas _).sub (h_meas _))
  rw [← condMutualInfo_of_inj_map hmij hmij hm0123 (fun z x ↦ (x, x - z)),
    condMutualInfo_comm hmf hmij,
    ← condMutualInfo_of_inj_map hmij hmf hm0123 (fun z x ↦ (x + z, x)),
    condMutualInfo_comm hmg hmf]
  · congr 1
    { ext ω
      { simp only [comp_apply, Pi.sub_apply, sub_sub_cancel] }
      { simp only [comp_apply, Pi.sub_apply, sub_sub_cancel] } }
    { rw [sub_sub, add_sub_left_comm, ← sub_sub]
      ext ω
      { simp only [comp_apply, Pi.sub_apply, add_sub_cancel] }
      { simp only [comp_apply, Pi.sub_apply, sub_sub_cancel] } }
  · exact fun _ _ _ h ↦ (Prod.ext_iff.1 h).2
  exact fun _ _ _ h ↦ (Prod.ext_iff.1 h).1


/-- Let $Y_1,Y_2,Y_3$ and $Y_4$ be independent $G$-valued random variables.
  Then
$$d[Y_1-Y_3; Y_2-Y_4] + d[Y_1|Y_1-Y_3; Y_2|Y_2-Y_4] $$
$$ + I[Y_1-Y_2 : Y_2 - Y_4 | Y_1-Y_2-Y_3+Y_4] = d[Y_1; Y_2] + d[Y_3; Y_4].$$
-/
lemma sum_of_rdist_eq (Y : Fin 4 → Ω → G) (h_indep : iIndepFun (fun _ : Fin 4 ↦ hG) Y μ)
  (h_meas : ∀ i, Measurable (Y i)) :
    d[Y 0; μ # Y 1; μ] + d[Y 2; μ # Y 3; μ]
      = d[(Y 0) - (Y 2); μ # (Y 1) - (Y 3); μ]
        + d[Y 0 | (Y 0) - (Y 2); μ # Y 1 | (Y 1) - (Y 3); μ]
        + I[(Y 0) - (Y 1) : (Y 1) - (Y 3) | (Y 0) - (Y 1) - (Y 2) + (Y 3); μ] := by
  let π : G × G →+ G := (AddMonoidHom.fst G G) - (AddMonoidHom.snd G G)
  have hπ {W_1 W_2 : Ω → G} : π ∘ ⟨W_1, W_2⟩ = W_1 - W_2 := rfl
  let Z_1 : Ω → G × G := ⟨Y 0, Y 2⟩
  let Z_2 : Ω → G × G := ⟨Y 1, Y 3⟩
  have hZ : Z_1 - Z_2 = ⟨Y 0 - Y 1, Y 2 - Y 3⟩ := rfl
  have m1 : Measurable Z_1 := (h_meas 0).prod_mk (h_meas 2)
  have m2 : Measurable Z_2 := (h_meas 1).prod_mk (h_meas 3)
  have h_indep_0 : IndepFun (Y 0) (Y 1) μ := h_indep.indepFun (by decide)
  have h_indep_2 : IndepFun (Y 2) (Y 3) μ := h_indep.indepFun (by decide)
  have h_indep_Z : IndepFun Z_1 Z_2 μ := h_indep.indepFun_prod_mk_prod_mk h_meas
    0 2 1 3 (by decide) (by decide) (by decide) (by decide)
  have h_indep_sub : IndepFun (Y 0 - Y 1) (Y 2 - Y 3) μ :=
    h_indep.indepFun_sub_sub h_meas 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
  have msub (i j : Fin 4) : Measurable (Y i - Y j) := (h_meas i).sub (h_meas j)
  have h_add : d[Z_1; μ # Z_2; μ] = d[Y 0; μ # Y 1; μ] + d[Y 2; μ # Y 3; μ] := by
    rw [h_indep_0.rdist_eq (h_meas 0) (h_meas 1), h_indep_2.rdist_eq (h_meas 2) (h_meas 3),
      h_indep_Z.rdist_eq m1 m2, hZ,
      (entropy_pair_eq_add (h_meas 0) (h_meas 2)).2 (h_indep.indepFun (by decide)),
      (entropy_pair_eq_add (h_meas 1) (h_meas 3)).2 (h_indep.indepFun (by decide)),
      (entropy_pair_eq_add (msub 0 1) (msub 2 3)).2 h_indep_sub]
    ring_nf
  rw [← h_add, rdist_of_indep_eq_sum_fibre π h_indep_Z m1 m2]
  simp only [hπ, hZ]
  rw [sum_of_rdist_eq_step_condRuzsaDist h_indep h_meas,
    sum_of_rdist_eq_step_condMutualInfo h_meas]

/-- Let $Y_1,Y_2,Y_3$ and $Y_4$ be independent $G$-valued random variables.
  Then
$$d[Y_1+Y_3; Y_2+Y_4] + d[Y_1|Y_1+Y_3; Y_2|Y_2+Y_4] $$
$$ + I[Y_1+Y_2 : Y_2 + Y_4 | Y_1+Y_2+Y_3+Y_4] = d[Y_1; Y_2] + d[Y_3; Y_4].$$
-/
lemma sum_of_rdist_eq_char_2
  [Module (ZMod 2) G] (Y : Fin 4 → Ω → G) (h_indep : iIndepFun (fun _ : Fin 4 ↦ hG) Y μ)
  (h_meas : ∀ i, Measurable (Y i)) :
    d[Y 0; μ # Y 1; μ] + d[Y 2; μ # Y 3; μ]
      = d[(Y 0) + (Y 2); μ # (Y 1) + (Y 3); μ]
        + d[Y 0 | (Y 0) + (Y 2); μ # Y 1 | (Y 1) + (Y 3); μ]
        + I[(Y 0) + (Y 1) : (Y 1) + (Y 3) | (Y 0) + (Y 1) + (Y 2) + (Y 3); μ] := by
  simpa [ZModModule.sub_eq_add] using sum_of_rdist_eq Y h_indep h_meas

lemma sum_of_rdist_eq_char_2' [Module (ZMod 2) G] (X Y X' Y' : Ω → G)
  (h_indep : iIndepFun (fun _ : Fin 4 ↦ hG) ![X, Y, X', Y'] μ)
  (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y') :
  d[X ; μ # Y ; μ] + d[X' ; μ # Y' ; μ]
    = d[X + X' ; μ # Y + Y' ; μ] + d[X | X + X' ; μ # Y | Y + Y' ; μ]
      + I[X + Y : Y + Y' | X + Y + X' + Y' ; μ] := by
  apply sum_of_rdist_eq_char_2 _ h_indep (fun i ↦ by fin_cases i <;> assumption)
