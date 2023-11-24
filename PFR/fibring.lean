import Mathlib.Probability.Independence.Basic
import PFR.Entropy.Basic
import PFR.ruzsa_distance

/-!
# The fibring identity

The proof of the fibring identity, which is a key component of the proof of PFR.

## Main statement

* `sum_of_rdist_eq`: If $Y_1,Y_2,Y_3,Y_4$ are independent, then $d[Y_1; Y_2] + d[ Y_3; Y_4]$ is equal to the sum of
$$d[Y_1+Y_3; Y_2+Y_4] + d[Y_1|Y_1+Y_3; Y_2|Y_2+Y_4] $$
and
$$ I[ Y_1+Y_2 : Y_2 + Y_4 | Y_1+Y_2+Y_3+Y_4 ].$$

-/

open MeasureTheory ProbabilityTheory

section GeneralFibring

-- $\pi : H \to H'$ is a homomorphism between additive groups.
variable {H : Type*} [AddCommGroup H] [Fintype H] {H' : Type*} [AddCommGroup H'] [Fintype H'] (π : H →+ H')
variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω'] {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- If $Z_1, Z_2$ are independent, then $d[Z_1; Z_2]$ is equal to
$$ d[\pi(Z_1);\pi(Z_2)] + d[Z_1|\pi(Z_1); Z_2 |\pi(Z_2)]$$
plus
$$I( Z_1 - Z_2 : (\pi(Z_1), \pi(Z_2))  |  \pi(Z_1 - Z_2) ).$$
-/
lemma rdist_of_indep_eq_sum_fibre {Z_1 Z_2: Ω → H} (h: IndepFun Z_1 Z_2 μ)
    (h1 : Measurable Z_1) (h2 : Measurable Z_2) :
    d[Z_1; μ # Z_2; μ] = d[π ∘ Z_1; μ # π ∘ Z_2; μ] + d[Z_1|π∘Z_1; μ # Z_2|π∘Z_2; μ] + I[ Z_1-Z_2 : ⟨ π∘Z_1, π∘Z_2⟩ | π∘(Z_1 - Z_2); μ] := by
  have hπ : Measurable π := measurable_from_top
  have comp_sub : π ∘ (Z_1 - Z_2) = π ∘ Z_1 - π ∘ Z_2 := by
      ext
      simp
  have step1 : d[Z_1; μ # Z_2; μ] = d[π ∘ Z_1; μ # π ∘ Z_2; μ] +
      H[(Z_1 - Z_2)| π ∘ (Z_1 - Z_2); μ] - H[Z_1 | π ∘ Z_1; μ] / 2 - H[Z_2 | π ∘ Z_2; μ] / 2 := by
    have hsub : H[(Z_1 - Z_2)| π ∘ (Z_1 - Z_2); μ] = H[(Z_1 - Z_2); μ] - H[π ∘ (Z_1 - Z_2); μ] :=
      condEntropy_comp_self (h1.sub h2) hπ
    rw [h.rdist_eq h1 h2, (h.comp hπ hπ).rdist_eq (hπ.comp h1) (hπ.comp h2),
      condEntropy_comp_self h1 hπ, condEntropy_comp_self h2 hπ, hsub, comp_sub]
    ring_nf
  have m0 : Measurable (fun x ↦ (x, π x)) := measurable_from_top
  have h' : IndepFun (⟨Z_1, π ∘ Z_1⟩) (⟨Z_2, π ∘ Z_2⟩) μ := h.comp m0 m0
  have m1 : Measurable (Z_1 - Z_2) := h1.sub h2
  have m2 : Measurable (⟨↑π ∘ Z_1, ↑π ∘ Z_2⟩) := (hπ.comp h1).prod_mk (hπ.comp h2)
  have m3 : Measurable (↑π ∘ (Z_1 - Z_2)) := hπ.comp m1
  have entroplem : H[Z_1 - Z_2|⟨⟨↑π ∘ Z_1, ↑π ∘ Z_2⟩, ↑π ∘ (Z_1 - Z_2)⟩; μ]
      = H[Z_1 - Z_2|⟨↑π ∘ Z_1, ↑π ∘ Z_2⟩; μ] := by
    rw [comp_sub]
    let f : H' × H' → (H' × H') × H' := fun (x,y) ↦ ((x,y), x - y)
    have hf : Function.Injective f := fun _ _ h ↦ (Prod.ext_iff.1 h).1
    have mf : Measurable f := measurable_id.prod_mk measurable_sub
    refine condEntropy_of_inj_map' μ m1 m2 f hf (mf.comp m2)
  rw [step1, condMutualInformation_eq' m1 m2 m3, entroplem,
    cond_rdist_of_indep h1 (hπ.comp h1) h2 (hπ.comp h2) μ h']
  ring_nf

lemma rdist_le_sum_fibre {Z_1: Ω → H} {Z_2: Ω' → H} (h1 : Measurable Z_1) (h2 : Measurable Z_2) :
    d[Z_1; μ # Z_2; μ'] ≥ d[π ∘ Z_1; μ # π ∘ Z_2; μ'] + d[Z_1|π∘Z_1; μ # Z_2|π∘Z_2; μ'] := by
  obtain ⟨ν, W_1, W_2, hν, m1, m2, hi, hi1, hi2⟩ :=  ProbabilityTheory.independent_copies h1 h2 μ μ'
  have hπ : Measurable π := measurable_from_top
  have hφ : Measurable (fun x ↦ (x, π x)) := measurable_from_top
  have hπ1 : IdentDistrib (⟨Z_1, π ∘ Z_1⟩) (⟨W_1, π ∘ W_1⟩) μ ν := hi1.symm.comp hφ
  have hπ2 : IdentDistrib (⟨Z_2, π ∘ Z_2⟩) (⟨W_2, π ∘ W_2⟩) μ' ν := hi2.symm.comp hφ
  rw [← hi1.rdist_eq hi2, ← (hi1.comp hπ).rdist_eq (hi2.comp hπ),
    rdist_of_indep_eq_sum_fibre π hi m1 m2, cond_rdist_of_copy hπ1 hπ2]
  exact le_add_of_nonneg_right (condMutualInformation_nonneg (m1.sub m2) (Measurable.prod_mk (hπ.comp m1) (hπ.comp m2)) _ _)

end GeneralFibring

variable {G : Type*} [AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Let $Y_1,Y_2,Y_3$ and $Y_4$ be independent $G$-valued random variables.
  Then
$$d[Y_1+Y_3; Y_2+Y_4] + d[Y_1|Y_1+Y_3; Y_2|Y_2+Y_4] $$
$$  + I[ Y_1+Y_2 : Y_2 + Y_4 | Y_1+Y_2+Y_3+Y_4 ] = d[Y_1; Y_2] + d[ Y_3; Y_4].$$
-/
lemma sum_of_rdist_eq (Y : ∀ i : Fin 3, Ω → G) (h_indep: iIndepFun (fun i : Fin 3 ↦ hG) Y μ) :
    d[Y 0; μ # Y 1; μ] + d[Y 2; μ # Y 3; μ ]
      = d[ (Y 0) + (Y 2); μ # (Y 1) + (Y 3); μ]
        + d[ Y 0 | (Y 0) + (Y 2); μ # Y 1 | (Y 1) + (Y 3); μ]
        + I[ (Y 0) + (Y 1) : (Y 1) + (Y 3) | (Y 0) + (Y 1) + (Y 2) + (Y 3); μ] := by sorry
