import PFR.Fibring
import PFR.TauFunctional
import PFR.Endgame
import PFR.EntropyPFR
import PFR.Main

/-!
# Improved PFR

An improvement to PFR that lowers the exponent from 12 to 11.

## Main results

*
-/

open MeasureTheory ProbabilityTheory


section GeneralInequality

variable {G : Type*} [AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {Ω₀ : Type*} [MeasureSpace Ω₀]  [IsProbabilityMeasure (ℙ : Measure Ω₀)]

variable (Y : Ω₀ → G) (hY : Measurable Y)

variable (Z₁ Z₂ Z₃ Z₄ : Ω → G)
  (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) (hZ₃ : Measurable Z₃) (hZ₄ : Measurable Z₄)

variable (h_indep : iIndepFun (fun _i => hG) ![Z₁, Z₂, Z₃, Z₄])

local notation3 "Sum" => Z₁ + Z₂ + Z₃ + Z₄

open scoped BigOperators

lemma gen_ineq_aux1 :
    d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] ≤ d[Y # Z₁]
      + (d[Z₁ # Z₂] + d[Z₁ # Z₃] + d[Z₂ # Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 2
      + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₁]) / 4 := by
  have hS : Measurable Sum := ((hZ₁.add' hZ₂).add' hZ₃).add' hZ₄
  have C : d[Z₁ # Z₃] + d[Z₂ # Z₄] = d[Z₁ + Z₂ # Z₃ + Z₄]
           + d[Z₁|Z₁ + Z₂ # Z₃|Z₃ + Z₄] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum] := by
    have M : d[Z₃ # Z₁] + d[Z₄ # Z₂] = d[Z₃ + Z₄ # Z₁ + Z₂]
           + d[Z₃|Z₃ + Z₄ # Z₁|Z₁ + Z₂] + I[Z₃ + Z₁ : Z₁ + Z₂ | Z₃ + Z₁ + Z₄ + Z₂] := by
      apply sum_of_rdist_eq_char_2 ![Z₃, Z₁, Z₄, Z₂] h_indep.reindex_four_cadb (fun i ↦ ?_)
      fin_cases i <;> assumption
    have J1 : Z₃ + Z₁ + Z₄ + Z₂ = Z₁ + Z₂ + Z₃ + Z₄ := by abel
    have J2 : Z₃ + Z₁ = Z₁ + Z₃ := by abel
    simp_rw [J1, J2] at M
    simpa only [rdist_symm (Y := Z₁), rdist_symm (X := Z₄), rdist_symm (X := Z₃ + Z₄),
      condRuzsaDist_symm hZ₃ (hZ₃.add' hZ₄) hZ₁ (hZ₁.add' hZ₂),
      condMutualInfo_comm (hZ₁.add' hZ₃) (hZ₁.add' hZ₂)] using M
  calc
  d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩]
    ≤ d[Y # Z₁ + Z₂ | Sum] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum]/2 :=
      condRuzsaDist_le'_prod (ℙ : Measure Ω₀) (ℙ : Measure Ω) hY (hZ₁.add hZ₂) (hZ₁.add hZ₃) hS
  _ ≤ d[Y # Z₁ + Z₂] + (d[Z₁ + Z₂ # Z₃ + Z₄] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum]) / 2
        + (H[Z₁ + Z₂] - H[Z₃ + Z₄]) / 4 := by
      have I : IndepFun (Z₁ + Z₂) (Z₃ + Z₄) := by
        exact h_indep.indepFun_add_add (ι := Fin 4) (by intro i; fin_cases i <;> assumption)
          0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      have J1 : (fun a ↦ Z₁ a + Z₂ a) + (fun a ↦ Z₃ a + Z₄ a) = Sum := by ext; simp; abel
      have J2 : (fun a ↦ Z₁ a + Z₂ a) = Z₁ + Z₂ := rfl
      have J3 : (fun a ↦ Z₃ a + Z₄ a) = Z₃ + Z₄ := rfl
      have A := condRuzsaDist_diff_le''' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY (hZ₁.add hZ₂)
        (hZ₃.add hZ₄) I
      rw [J1, J2, J3] at A
      linarith
  _ ≤ d[Y # Z₁] + (d[Z₁ # Z₂] + d[Z₁ + Z₂ # Z₃ + Z₄] + I[Z₁ + Z₂ : Z₁ + Z₃ | Sum]) / 2
        + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₁]) / 4 := by
      have I : IndepFun Z₁ Z₂ := by exact h_indep.indepFun (show 0 ≠ 1 by decide)
      have A := condRuzsaDist_diff_le' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY hZ₁ hZ₂ I
      linarith
  _ = _ := by linarith

/-- If `B` is independent from `C`, then conditioning on an event given by `C` does not change
the distribution of `B`. -/
lemma ProbabilityTheory.IndepFun.identDistrib_cond {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Ω → G} {C : Ω → S} [MeasurableSpace S] (hi : IndepFun B C μ) {s : Set S}
    (hs : MeasurableSet s) (hB : Measurable B) (hC : Measurable C)
    (h : μ (C ⁻¹' s) ≠ 0) :
    IdentDistrib B B μ (μ[|C ⁻¹' s]) := by
  refine ⟨hB.aemeasurable, hB.aemeasurable, ?_⟩
  ext t ht
  rw [Measure.map_apply hB ht, Measure.map_apply hB ht, cond_apply _ (hC hs), Set.inter_comm,
    hi.measure_inter_preimage_eq_mul ht hs, mul_comm, mul_assoc,
    ENNReal.mul_inv_cancel h (by finiteness), mul_one]

lemma condRuszaDist_prod_eq_of_indepFun
    {A : Ω₀ → G} {B C D : Ω → G} (hA : Measurable A) (hB : Measurable B) (hC : Measurable C)
    (hD : Measurable D) (h : IndepFun (⟨B, C⟩) D) :
    d[A # B | ⟨C, D⟩] = d[A # B | C] := by
  rw [condRuzsaDist'_prod_eq_sum' _ _ hB hC hD]
  have : d[A # B | C] = ∑ z, (ℙ (D ⁻¹' {z})).toReal * d[A # B | C] := by
    rw [← Finset.sum_mul, sum_measure_preimage_singleton' ℙ hD, one_mul]
  rw [this]
  congr with w
  rcases eq_or_ne (ℙ (D ⁻¹' {w})) 0 with hw|hw
  · simp [hw]
  congr 1
  apply condRuzsaDist'_of_copy _ hB hC _ hB hC (IdentDistrib.refl hA.aemeasurable)
  exact (h.identDistrib_cond (MeasurableSet.singleton w) (hB.prod_mk hC) hD hw).symm

lemma condEntropy_prod_eq_of_indepFun
    {B C D : Ω → G} (hB : Measurable B) (hC : Measurable C)
    (hD : Measurable D) (h : IndepFun (⟨B, C⟩) D) :
    H[B | ⟨C, D⟩] = H[B | C] := by
  rw [condEntropy_prod_eq_sum _ hC hD]
  have : H[B | C] = ∑ z, (ℙ (D ⁻¹' {z})).toReal * H[B | C] := by
    rw [← Finset.sum_mul, sum_measure_preimage_singleton' ℙ hD, one_mul]
  rw [this]
  congr with w
  rcases eq_or_ne (ℙ (D ⁻¹' {w})) 0 with hw|hw
  · simp [hw]
  congr 1
  have : IsProbabilityMeasure (ℙ[|D ⁻¹' {w}]) := cond_isProbabilityMeasure ℙ hw
  apply IdentDistrib.condEntropy_eq hB hC hB hC
  exact (h.identDistrib_cond (MeasurableSet.singleton w) (hB.prod_mk hC) hD hw).symm

/-- If `Z₁` is independent of `Z₂`, then they remain independent when conditioning on an event
of the form `Z₁ ∈ s` of positive probability. -/
lemma ProbabilityTheory.IndepFun.cond_left {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} {Z₁ : Ω → G} {Z₂ : Ω → S}
    [MeasurableSpace S]
    (h : IndepFun Z₁ Z₂ μ) [IsFiniteMeasure μ] {s : Set G} (hne : μ (Z₁ ⁻¹' s) ≠ 0)
    (hs : MeasurableSet s) (hZ₁ : Measurable Z₁) :
    IndepFun Z₁ Z₂ (μ[| Z₁⁻¹' s]) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.2 (fun u v hu hv ↦ ?_)
  have : Z₁ ⁻¹' s ∩ (Z₁ ⁻¹' u ∩ Z₂ ⁻¹' v) = Z₁ ⁻¹' (s ∩ u) ∩ Z₂ ⁻¹' v := by aesop
  simp only [cond_apply _ (hZ₁ hs), this]
  rw [h.measure_inter_preimage_eq_mul (hs.inter hu) hv, Set.preimage_inter,
    h.measure_inter_preimage_eq_mul hs hv, ← mul_assoc (μ (Z₁ ⁻¹' s))⁻¹,
    ← mul_assoc (μ (Z₁ ⁻¹' s))⁻¹, ENNReal.inv_mul_cancel hne (by finiteness), one_mul]

theorem kernelIndepsymm {Ω α β γ : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α}
    {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {κ : kernel α Ω} {f : Ω → β} {g : Ω → γ}
    {μ : Measure α}
    (hfg : kernel.IndepFun f g κ μ) : kernel.IndepFun g f κ μ :=
  kernel.Indep.symm hfg

theorem ProbabilityTheory.IndepFun.symm' {γ β Ω : Type*} {_ : MeasurableSpace γ}
    {_ : MeasurableSpace β} {_ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → γ}
    (hfg : IndepFun f g μ) :
    IndepFun g f μ := kernelIndepsymm hfg

/-- If `Z₁` is independent of `Z₂`, then they remain independent when conditioning on an event
of the form `Z₂ ∈ t` of positive probability. -/
lemma ProbabilityTheory.IndepFun.cond_right {Ω : Type*} {_ : MeasurableSpace Ω}
    {μ : Measure Ω} {Z₁ : Ω → G} {Z₂ : Ω → S}
    [MeasurableSpace S]
    (h : IndepFun Z₁ Z₂ μ) [IsFiniteMeasure μ] {t : Set S} (hne : μ (Z₂ ⁻¹' t) ≠ 0)
    (ht : MeasurableSet t) (hZ₂ : Measurable Z₂) :
    IndepFun Z₁ Z₂ (μ[| Z₂⁻¹' t]) :=
  (h.symm'.cond_left hne ht hZ₂).symm'

/-- If `Z₁` is independent of `Z₂`, then they remain independent when conditioning on an event
of the form `Z₁ ∈ s ∩ Z₂ ∈ t` of positive probability. -/
lemma ProbabilityTheory.IndepFun.cond
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} {Z₁ : Ω → G} {Z₂ : Ω → S}
    [MeasurableSpace S] [IsFiniteMeasure μ] (h : IndepFun Z₁ Z₂ μ)
    {s : Set G} {t : Set S} (hne : μ (Z₁ ⁻¹' s) ≠ 0) (hne' : μ (Z₂ ⁻¹' t) ≠ 0)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂) :
    IndepFun Z₁ Z₂ (μ[| Z₁ ⁻¹' s ∩ Z₂⁻¹' t]) := by
  have A : μ (Z₁ ⁻¹' s ∩ Z₂ ⁻¹' t) ≠ 0 := by
    rw [h.measure_inter_preimage_eq_mul hs ht]
    simp [hne, hne']
  have B : (μ[| Z₁ ⁻¹' s]) (Z₂ ⁻¹' t) ≠ 0 := by
    rw [cond_apply _ (hZ₁ hs)]
    simp [A]
    finiteness
  convert (h.cond_left hne hs hZ₁).cond_right B ht hZ₂ using 1
  rw [cond_cond_eq_cond_inter' _ (hZ₁ hs) (hZ₂ ht) (by finiteness) A]

lemma gen_ineq_aux2 :
    d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] ≤ d[Y # Z₁]
      + (d[Z₁ # Z₃] + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]) / 2
      + (H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃] + H[Z₁] - H[Z₃]) / 4 := by
  have hS : Measurable Sum := ((hZ₁.add' hZ₂).add' hZ₃).add' hZ₄
  have I : IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩) := by
    apply (h_indep.indepFun_prod_prod ?_ 0 2 1 3
      (by decide) (by decide) (by decide) (by decide))
    intro i; fin_cases i <;> assumption
  calc
  d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩]
    = d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩] := by
      let e : G × G ≃ G × G :=
        { toFun := fun p ↦ ⟨p.1, p.2 - p.1⟩
          invFun := fun p ↦ ⟨p.1, p.2 + p.1⟩
          left_inv := by intro ⟨a, b⟩; simp [add_assoc]
          right_inv := by intro ⟨a, b⟩; simp [add_assoc] }
      convert (condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂)
        (⟨Z₁ + Z₃, Sum⟩) e (hZ₁.add' hZ₂) ((hZ₁.add' hZ₃).prod_mk hS)
        (measurable_discrete e) e.injective).symm
      simp only [Pi.add_apply, Equiv.coe_fn_mk, Function.comp_apply]
      abel
  _ = ∑ w, (ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w})).toReal *
        d[Y ; ℙ # Z₁ + Z₂ ; ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]] := by
    rw [condRuzsaDist'_eq_sum' (hZ₁.add' hZ₂) ((hZ₁.add' hZ₃).prod_mk (hZ₂.add' hZ₄))]
  _ ≤ ∑ w, (ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w})).toReal * (d[Y ; ℙ # Z₁ ; ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]]
      + d[Z₁ ; ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w}] # Z₂ ; ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w}]] / 2
      + H[Z₂ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w] / 4 - H[Z₁ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w] / 4) := by
    apply Finset.sum_le_sum (fun w h'w ↦ ?_)
    rcases eq_or_ne (ℙ (⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w})) 0 with hw|hw
    · simp [hw]
    gcongr
    have : IsProbabilityMeasure (ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w]) := cond_isProbabilityMeasure ℙ hw
    have : IndepFun Z₁ Z₂ (ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w}]) := by
      have E : (⟨Z₁, Z₃⟩)⁻¹' {p | p.1 + p.2 = w.1} ∩ (⟨Z₂, Z₄⟩)⁻¹' {p | p.1 + p.2 = w.2}
        = ⟨Z₁ + Z₃, Z₂ + Z₄⟩ ⁻¹' {w} := by aesop
      rw [← E, I.measure_inter_preimage_eq_mul] at hw
      swap; exact measurable_add (measurableSet_singleton _)
      swap; exact measurable_add (measurableSet_singleton _)
      simp only [ne_eq, mul_eq_zero, not_or] at hw
      have I : IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩) (ℙ[|(⟨Z₁, Z₃⟩)⁻¹' {p | p.1 + p.2 = w.1}
          ∩ (⟨Z₂, Z₄⟩)⁻¹' {p | p.1 + p.2 = w.2}]) :=
        I.cond hw.1 hw.2 (measurable_add (measurableSet_singleton w.1))
          (measurable_add (measurableSet_singleton w.2)) (hZ₁.prod_mk hZ₃) (hZ₂.prod_mk hZ₄)
      rw [E] at I
      exact I.comp measurable_fst measurable_fst
    have := condRuzsaDist_diff_le' (ℙ : Measure Ω₀) (μ' := ℙ[|⟨Z₁ + Z₃, Z₂ + Z₄⟩ ← w])
      hY hZ₁ hZ₂ this
    linarith
  _ = d[Y # Z₁ | Z₁ + Z₃] + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]/2
      + H[Z₂ | Z₂ + Z₄] / 4 - H[Z₁ | Z₁ + Z₃] / 4 := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_div]
    congr
    · rw [← condRuzsaDist'_eq_sum' hZ₁ ((hZ₁.add' hZ₃).prod_mk (hZ₂.add' hZ₄))]
      apply condRuszaDist_prod_eq_of_indepFun hY hZ₁ (hZ₁.add' hZ₃)
        (hZ₂.add' hZ₄)
      exact I.comp (measurable_fst.prod_mk measurable_add) measurable_add
    · simp_rw [← mul_div_assoc, ← Finset.sum_div]
      rw [condRuzsaDist_eq_sum' hZ₁ (hZ₁.add' hZ₃) hZ₂ (hZ₂.add' hZ₄), Fintype.sum_prod_type]
      congr with x
      congr with y
      have : (⟨Z₁ + Z₃, Z₂ + Z₄⟩) ⁻¹' {(x, y)} = (Z₁ + Z₃) ⁻¹' {x} ∩ (Z₂ + Z₄) ⁻¹' {y} := by
        ext p; simp
      rw [this]
      have J : IndepFun (Z₁ + Z₃) (Z₂ + Z₄) := by exact I.comp measurable_add measurable_add
      rw [J.measure_inter_preimage_eq_mul (measurableSet_singleton x) (measurableSet_singleton y),
        ENNReal.toReal_mul]
      rcases eq_or_ne (ℙ ((Z₁ + Z₃) ⁻¹' {x})) 0 with h1|h1
      · simp [h1]
      rcases eq_or_ne (ℙ ((Z₂ + Z₄) ⁻¹' {y})) 0 with h2|h2
      · simp [h2]
      congr 1
      have A : IdentDistrib Z₁ Z₁ (ℙ[|(Z₁ + Z₃) ⁻¹' {x} ∩ (Z₂ + Z₄) ⁻¹' {y}])
          (ℙ[|(Z₁ + Z₃) ⁻¹' {x}]) := by
        rw [← cond_cond_eq_cond_inter'' ((hZ₁.add' hZ₃) (measurableSet_singleton _))
          ((hZ₂.add' hZ₄) (measurableSet_singleton _))]
        have : IsProbabilityMeasure (ℙ[|(Z₁ + Z₃) ⁻¹' {x}]) := cond_isProbabilityMeasure _ h1
        apply (IndepFun.identDistrib_cond _ (measurableSet_singleton _) hZ₁ (hZ₂.add' hZ₄) _).symm
        · have : IndepFun (⟨Z₁, Z₃⟩) (⟨Z₂, Z₄⟩) (ℙ[|(⟨Z₁, Z₃⟩) ⁻¹' {p | p.1 + p.2 = x}]) :=
            I.cond_left (by exact h1) (measurable_add (measurableSet_singleton x))
              (hZ₁.prod_mk hZ₃)
          exact this.comp measurable_fst measurable_add
        · rw [cond_apply _ ((hZ₁.add' hZ₃) (measurableSet_singleton x)),
            J.measure_inter_preimage_eq_mul (measurableSet_singleton x) (measurableSet_singleton y)]
          simp [h1, h2]
          finiteness
      have B : IdentDistrib Z₂ Z₂ (ℙ[|(Z₁ + Z₃) ⁻¹' {x} ∩ (Z₂ + Z₄) ⁻¹' {y}])
          (ℙ[|(Z₂ + Z₄) ⁻¹' {y}]) := by
        rw [Set.inter_comm, ← cond_cond_eq_cond_inter'' ((hZ₂.add' hZ₄) (measurableSet_singleton _))
          ((hZ₁.add' hZ₃) (measurableSet_singleton _))]
        have : IsProbabilityMeasure (ℙ[|(Z₂ + Z₄) ⁻¹' {y}]) := cond_isProbabilityMeasure _ h2
        apply (IndepFun.identDistrib_cond _ (measurableSet_singleton _) hZ₂ (hZ₁.add' hZ₃) _).symm
        · have : IndepFun (⟨Z₂, Z₄⟩) (⟨Z₁, Z₃⟩) (ℙ[|(⟨Z₂, Z₄⟩) ⁻¹' {p | p.1 + p.2 = y}]) :=
            I.symm.cond_left (by exact h2) (measurable_add (measurableSet_singleton y))
              (hZ₂.prod_mk hZ₄)
          exact this.comp measurable_fst measurable_add
        · rw [cond_apply _ ((hZ₂.add' hZ₄) (measurableSet_singleton y)),
            J.symm.measure_inter_preimage_eq_mul (measurableSet_singleton y)
              (measurableSet_singleton x)]
          simp [h1, h2]
          finiteness
      exact IdentDistrib.rdist_eq A B
    · have I1 : H[Z₂ | Z₂ + Z₄] = H[Z₂ | ⟨Z₂ + Z₄, Z₁ + Z₃⟩] := by
        apply (condEntropy_prod_eq_of_indepFun hZ₂ (hZ₂.add' hZ₄) (hZ₁.add' hZ₃) _).symm
        exact I.symm.comp (measurable_fst.prod_mk measurable_add) measurable_add
      have I2 : H[Z₂ | ⟨Z₂ + Z₄, Z₁ + Z₃⟩] = H[Z₂ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩] :=
        condEntropy_of_injective' _ hZ₂ ((hZ₁.add' hZ₃).prod_mk (hZ₂.add' hZ₄))
          _ (Equiv.prodComm G G).injective ((hZ₂.add' hZ₄).prod_mk (hZ₁.add' hZ₃))
      rw [I1, I2, condEntropy_eq_sum_fintype _ _ _ ((hZ₁.add' hZ₃).prod_mk (hZ₂.add' hZ₄))]
      simp_rw [← mul_div_assoc, Finset.sum_div]
    · have : H[Z₁ | Z₁ + Z₃] = H[Z₁ | ⟨Z₁ + Z₃, Z₂ + Z₄⟩] := by
        apply (condEntropy_prod_eq_of_indepFun hZ₁ (hZ₁.add' hZ₃) (hZ₂.add' hZ₄) _).symm
        exact I.comp (measurable_fst.prod_mk measurable_add) measurable_add
      rw [this, condEntropy_eq_sum_fintype _ _ _ ((hZ₁.add' hZ₃).prod_mk (hZ₂.add' hZ₄))]
      simp_rw [← mul_div_assoc, Finset.sum_div]
  _ ≤ (d[Y # Z₁] + d[Z₁ # Z₃]/2 + H[Z₁]/4 - H[Z₃]/4) + d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄]/2
      + H[Z₂ | Z₂ + Z₄] / 4 - H[Z₁ | Z₁ + Z₃] / 4 := by
    gcongr
    have I : IndepFun Z₁ Z₃ := by exact h_indep.indepFun (show 0 ≠ 2 by decide)
    have := condRuzsaDist_diff_le''' (ℙ : Measure Ω₀) (μ' := (ℙ : Measure Ω)) hY hZ₁ hZ₃ I
    linarith
  _ = _ := by ring

/-- Let $Z_1, Z_2, Z_3, Z_4$ be independent $G$-valued random variables, and let $Y$ be another
$G$-valued random variable.  Set $S := Z_1+Z_2+Z_3+Z_4$. Then
$d[Y; Z_1+Z_2|Z_1 + Z_3, S] - d[Y; Z_1]$ is at most
$$ \tfrac{1}{4} (d[Z_1;Z_2] + 2d[Z_1;Z_3] + d[Z_2;Z_4])$$
$$+ \tfrac{1}{4}(d[Z_1|Z_1 + Z_3 ; Z_2|Z_2+Z_4] - d[Z_1|Z_1+Z_2 ; Z_3|Z_3+Z_4]])$$
$$+ \tfrac{1}{8} (\bbH[Z_1+Z_2] - \bbH[Z_3+Z_4] + \bbH[Z_2] - \bbH[Z_3]$$
$$ + \bbH[Z_2|Z_2+Z_4] - \bbH[Z_1|Z_1+Z_3]).$$
-/
lemma gen_ineq_00 : d[Y # Z₁ + Z₂ | ⟨Z₁ + Z₃, Sum⟩] - d[Y # Z₁] ≤
    (d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4
    + (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4
    + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8 := by
  have I1 := gen_ineq_aux1 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep
  have I2 := gen_ineq_aux2 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep
  linarith

/-- Other version of `gen_ineq_00`, in which we switch to the complement in the second term. -/
lemma gen_ineq_01 : d[Y # Z₁ + Z₂ | ⟨Z₂ + Z₄, Sum⟩] - d[Y # Z₁] ≤
    (d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4
    + (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4
    + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8 := by
  convert gen_ineq_00 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep using 2
  let e : G × G ≃ G × G :=
  { toFun := fun p ↦ ⟨p.2 - p.1, p.2⟩
    invFun := fun p ↦ ⟨- p.1 + p.2, p.2⟩
    left_inv := by intro ⟨a, b⟩; simp [add_comm b a, add_assoc]
    right_inv := by intro ⟨a, b⟩; simp [add_comm a b, ← add_assoc] }
  convert (condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂) (⟨Z₁ + Z₃, Sum⟩) e
    (by measurability) (by measurability) (by measurability) e.injective) with p
  simp only [Pi.add_apply, Equiv.coe_fn_mk, Function.comp_apply]
  abel

/-- Other version of `gen_ineq_00`, in which we switch to the complement in the first term. -/
lemma gen_ineq_10 : d[Y # Z₃ + Z₄ | ⟨Z₁ + Z₃, Sum⟩] - d[Y # Z₁] ≤
    (d[Z₁ # Z₂] + 2 * d[Z₁ # Z₃] + d[Z₂ # Z₄]) / 4
    + (d[Z₁ | Z₁ + Z₃ # Z₂ | Z₂ + Z₄] - d[Z₁ | Z₁ + Z₂ # Z₃ | Z₃ + Z₄]) / 4
    + (H[Z₁ + Z₂] - H[Z₃ + Z₄] + H[Z₂] - H[Z₃] + H[Z₂ | Z₂ + Z₄] - H[Z₁ | Z₁ + Z₃]) / 8 := by
  convert gen_ineq_00 Y hY Z₁ Z₂ Z₃ Z₄ hZ₁ hZ₂ hZ₃ hZ₄ h_indep using 2
  have hS : Measurable Sum := ((hZ₁.add' hZ₂).add' hZ₃).add' hZ₄
  let e : G × G ≃ G × G := Equiv.prodComm G G
  have A : e ∘ ⟨Z₁ + Z₃, Sum⟩ = ⟨Sum, Z₁ + Z₃⟩ := by ext p <;> rfl
  rw [← condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₃ + Z₄) (⟨Z₁ + Z₃, Sum⟩)
      e (by measurability) (by measurability) (by measurability) e.injective ,
      ← condRuzsaDist_comp_right (ℙ : Measure Ω₀) (ℙ : Measure Ω) Y (Z₁ + Z₂)
        (⟨Z₁ + Z₃, Sum⟩) e (by measurability) (by measurability) (by measurability)  e.injective, A,
      condRuzsaDist'_prod_eq_sum _ _ (hZ₃.add' hZ₄) hS (hZ₁.add' hZ₃),
      condRuzsaDist'_prod_eq_sum _ _ (hZ₁.add' hZ₂) hS (hZ₁.add' hZ₃)]
  congr with w
  rcases eq_or_ne (ℙ ((Z₁ + Z₃) ⁻¹' {w})) 0 with hw|hw
  · simp [hw]
  have : IsProbabilityMeasure (ℙ[|(Z₁ + Z₃) ⁻¹' {w}]) := cond_isProbabilityMeasure ℙ hw
  have : Sum = (Z₁ + Z₂) + (Z₃ + Z₄) := by abel
  rw [this, condRuzsaDist'_of_inj_map' hY (hZ₁.add' hZ₂) (hZ₃.add' hZ₄)]

end GeneralInequality

section MainEstimates

open MeasureTheory ProbabilityTheory

variable {G : Type*} [AddCommGroup G] [Fintype G] [hG : MeasurableSpace G]
  [MeasurableSingletonClass G] [ElementaryAddCommGroup G 2] [MeasurableAdd₂ G]

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable {p : refPackage Ω₀₁ Ω₀₂ G}

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {X₁ X₂ X₁' X₂' : Ω → G}
  (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₁' : Measurable X₁') (hX₂' : Measurable X₂')

variable (h₁ : IdentDistrib X₁ X₁') (h₂ : IdentDistrib X₂ X₂')

variable (h_indep : iIndepFun (fun _i => hG) ![X₁, X₂, X₂', X₁'])

variable (h_min: tau_minimizes p X₁ X₂)

/-- `k := d[X₁ # X₂]`, the Ruzsa distance `rdist` between X₁ and X₂. -/
local notation3 "k" => d[X₁ # X₂]

/-- `U := X₁ + X₂` -/
local notation3 "U" => X₁ + X₂

/-- `V := X₁' + X₂` -/
local notation3 "V" => X₁' + X₂

/-- `W := X₁' + X₁` -/
local notation3 "W" => X₁' + X₁

/-- `S := X₁ + X₂ + X₁' + X₂'` -/
local notation3 "S" => X₁ + X₂ + X₁' + X₂'

/-- `I₁ := I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₂` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₁" => I[X₁ + X₂ : X₁' + X₂ | X₁ + X₂ + X₁' + X₂']

/-- `I₂ := I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']`, the conditional mutual information
of `X₁ + X₂` and `X₁' + X₁` given the quadruple sum `X₁ + X₂ + X₁' + X₂'`. -/
local notation3 "I₂" => I[X₁ + X₂ : X₁' + X₁ | X₁ + X₂ + X₁' + X₂']

local notation3:max "c[" A "; " μ " # " B " ; " μ' "]" =>
  d[p.X₀₁; ℙ # A; μ] - d[p.X₀₁ # X₁] + (d[p.X₀₂; ℙ # B; μ'] - d[p.X₀₂ # X₂])

local notation3:max "c[" A " # " B "]" =>
  d[p.X₀₁ # A] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # B] - d[p.X₀₂ # X₂])

local notation3:max "c[" A " | " B " # " C " | " D "]" =>
  d[p.X₀₁ # A|B] - d[p.X₀₁ # X₁] + (d[p.X₀₂ # C|D] - d[p.X₀₂ # X₂])

section aux

variable {Ω' : Type*} [MeasureSpace Ω'] [IsProbabilityMeasure (ℙ : Measure Ω')]
variable {T₁ T₂ T₃ : Ω' → G} (hT : T₁ + T₂ + T₃ = 0)
variable (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃)

local notation3:max "δ[" μ "]" => I[T₁ : T₂ ; μ] + I[T₂ : T₃ ; μ] + I[T₃ : T₁ ; μ]
local notation3:max "δ" => I[T₁ : T₂] + I[T₂ : T₃] + I[T₃ : T₁]

local notation3:max "ψ[" A " # " B "]" => d[A # B] + p.η * (c[A # B])
local notation3:max "ψ[" A "; " μ " # " B " ; " μ' "]" =>
  d[A ; μ # B ; μ'] + p.η * c[A ; μ # B ; μ']

/-- For any $T_1, T_2, T_3$ adding up to $0$, then $k$ is at most
$$ \delta + \eta (d[X^0_1;T_1|T_3]-d[X^0_1;X_1]) + \eta (d[X^0_2;T_2|T_3]-d[X^0_2;X_2])$$
where $\delta = I[T₁ : T₂ ; μ] + I[T₂ : T₃ ; μ] + I[T₃ : T₁ ; μ]$. -/
lemma construct_good_prelim' : k ≤ δ + p.η * c[T₁ | T₃ # T₂ | T₃] := by
  let sum1 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]
  let sum2 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₁; ℙ # T₁; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₁ # X₁]]
  let sum3 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ d[p.X₀₂; ℙ # T₂; ℙ[|T₃ ⁻¹' {t}]] - d[p.X₀₂ # X₂]]
  let sum4 : ℝ := (Measure.map T₃ ℙ)[fun t ↦ ψ[T₁; ℙ[|T₃ ⁻¹' {t}] # T₂; ℙ[|T₃ ⁻¹' {t}]]]
  have h2T₃ : T₃ = T₁ + T₂ := by
    calc T₃ = T₁ + T₂ + T₃ - T₃ := by rw [hT, zero_sub]; simp
      _ = T₁ + T₂ := by rw [add_sub_cancel]
  have hP : IsProbabilityMeasure (Measure.map T₃ ℙ) := isProbabilityMeasure_map hT₃.aemeasurable
  -- control sum1 with entropic BSG
  have h1 : sum1 ≤ δ := by
    have h1 : sum1 ≤ 3 * I[T₁ : T₂] + 2 * H[T₃] - H[T₁] - H[T₂] := by
      subst h2T₃; exact ent_bsg hT₁ hT₂
    have h2 : H[⟨T₂, T₃⟩] = H[⟨T₁, T₂⟩]
    · rw [h2T₃, entropy_add_right', entropy_comm] <;> assumption
    have h3 : H[⟨T₁, T₂⟩] = H[⟨T₃, T₁⟩]
    · rw [h2T₃, entropy_add_left, entropy_comm] <;> assumption
    simp_rw [mutualInfo_def] at h1 ⊢; linarith
  -- rewrite sum2 and sum3 as Rusza distances
  have h2 : sum2 = d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁] := by

    simp only [integral_sub (integrable_of_fintype _ _) (integrable_of_fintype _ _), integral_const,
      measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul, sub_left_inj]
    simp_rw [condRuzsaDist'_eq_sum hT₁ hT₃, integral_eq_sum_finset' _ _ (FiniteRange.null_of_compl hT₃ _),
      Measure.map_apply hT₃ (measurableSet_singleton _), smul_eq_mul]

  have h3 : sum3 = d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂] := by
    simp only [integral_sub (integrable_of_fintype _ _) (integrable_of_fintype _ _), integral_const,
      measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul, sub_left_inj]
    simp_rw [condRuzsaDist'_eq_sum hT₂ hT₃, integral_eq_sum_finset' _ _ (FiniteRange.null_of_compl hT₃ _),
      Measure.map_apply hT₃ (measurableSet_singleton _), smul_eq_mul]
  -- put all these estimates together to bound sum4
  have h4 : sum4 ≤ δ + p.η * ((d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁])
      + (d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂])) := by
    have : sum4 = sum1 + p.η * (sum2 + sum3) := by
      simp only [integral_add (integrable_of_fintype _ _) (integrable_of_fintype _ _),
        integral_mul_left]
    rw [this, h2, h3, add_assoc, mul_add]
    linarith
  have hk : k ≤ sum4 := by
    suffices (Measure.map T₃ ℙ)[fun _ ↦ k] ≤ sum4 by simpa using this
    apply integral_mono_ae (integrable_of_fintype _ _) (integrable_of_fintype _ _)
    apply Countable.ae_of_singleton
    intros t ht
    have : IsProbabilityMeasure (ℙ[|T₃ ⁻¹' {t}]) :=
      cond_isProbabilityMeasure ℙ (by simpa [hT₃] using ht)
    dsimp only
    linarith only [distance_ge_of_min' (μ := ℙ[|T₃ ⁻¹' {t}]) (μ' := ℙ[|T₃ ⁻¹' {t}]) p h_min hT₁ hT₂]
  exact hk.trans h4

open ElementaryAddCommGroup

/-- In fact $k$ is at most
 $$ \delta + \frac{\eta}{6}  \sum_{i=1}^2 \sum_{1 \leq j,l \leq 3; j \neq l}
     (d[X^0_i;T_j|T_l] - d[X^0_i; X_i]).$$
-/
lemma construct_good_improved' : k ≤ δ
    + (p.η / 6) * ((d[p.X₀₁ # T₁ | T₂] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₁ | T₃] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₁ # T₂ | T₁] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₂ | T₃] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₁ # T₃ | T₁] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # T₃ | T₂] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₂ # T₁ | T₂] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₁ | T₃] - d[p.X₀₂ # X₂])
                 + (d[p.X₀₂ # T₂ | T₁] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₂ | T₃] - d[p.X₀₂ # X₂])
                 + (d[p.X₀₂ # T₃ | T₁] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # T₃ | T₂] - d[p.X₀₂ # X₂])) :=
    by
  have I1 : I[T₂ : T₁] = I[T₁ : T₂] := mutualInfo_comm hT₂ hT₁ _
  have I2 : I[T₃ : T₁] = I[T₁ : T₃] := mutualInfo_comm hT₃ hT₁ _
  have I3 : I[T₃ : T₂] = I[T₂ : T₃] := mutualInfo_comm hT₃ hT₂ _
  have Z123 := construct_good_prelim' h_min hT hT₁ hT₂ hT₃
  have h132 : T₁ + T₃ + T₂ = 0 := by rw [← hT]; abel
  have Z132 := construct_good_prelim' h_min h132 hT₁ hT₃ hT₂
  have h213 : T₂ + T₁ + T₃ = 0 := by rw [← hT]; abel
  have Z213 := construct_good_prelim' h_min h213 hT₂ hT₁ hT₃
  have h231 : T₂ + T₃ + T₁ = 0 := by rw [← hT]; abel
  have Z231 := construct_good_prelim' h_min h231 hT₂ hT₃ hT₁
  have h312 : T₃ + T₁ + T₂ = 0 := by rw [← hT]; abel
  have Z312 := construct_good_prelim' h_min h312 hT₃ hT₁ hT₂
  have h321 : T₃ + T₂ + T₁ = 0 := by rw [← hT]; abel
  have Z321 := construct_good_prelim' h_min h321 hT₃ hT₂ hT₁
  simp only [I1, I2, I3] at Z123 Z132 Z213 Z231 Z312 Z321
  linarith

/-- Rephrase `construct_good_improved'` with an explicit probability measure, as we will
apply it to (varying) conditional measures. -/
lemma construct_good_improved'' {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    [IsProbabilityMeasure μ] {T₁ T₂ T₃ : Ω' → G}
    (hT : T₁ + T₂ + T₃ = 0) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (hT₃ : Measurable T₃) :
    k ≤ I[T₁ : T₂ ; μ] + I[T₂ : T₃ ; μ] + I[T₃ : T₁ ; μ] + (p.η / 6) *
    ((d[p.X₀₁ ; ℙ # T₁ | T₂ ; μ] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ ; ℙ # T₁ | T₃ ; μ] - d[p.X₀₁ # X₁])
      + (d[p.X₀₁ ; ℙ # T₂ | T₁ ; μ] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ ; ℙ # T₂ | T₃ ; μ] - d[p.X₀₁ # X₁])
      + (d[p.X₀₁ ; ℙ # T₃ | T₁ ; μ] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ ; ℙ # T₃ | T₂ ; μ] - d[p.X₀₁ # X₁])
      + (d[p.X₀₂ ; ℙ # T₁ | T₂ ; μ] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ ; ℙ # T₁ | T₃ ; μ] - d[p.X₀₂ # X₂])
      + (d[p.X₀₂ ; ℙ # T₂ | T₁ ; μ] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ ; ℙ # T₂ | T₃ ; μ] - d[p.X₀₂ # X₂])
      + (d[p.X₀₂ ; ℙ # T₃ | T₁ ; μ] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ ; ℙ # T₃ | T₂ ; μ] - d[p.X₀₂ # X₂]))
    := by
  let M : MeasureSpace Ω' := ⟨μ⟩
  exact construct_good_improved' h_min hT hT₁ hT₂ hT₃

end aux

open scoped BigOperators

/--   $k$ is at most
$$ \leq I(U : V \, | \, S) + I(V : W \, | \,S) + I(W : U \, | \, S) + \frac{\eta}{6}  \sum_{i=1}^2 \sum_{A,B \in \{U,V,W\}: A \neq B} (d[X^0_i;A|B,S] - d[X^0_i; X_i]).$$
-/
lemma averaged_construct_good : k ≤ (I[U : V | S] + I[V : W | S] + I[W : U | S])
    + (p.η / 6) * (((d[p.X₀₁ # U | ⟨V, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # U | ⟨W, S⟩] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₁ # V | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # V | ⟨W, S⟩] - d[p.X₀₁ # X₁])
                 + (d[p.X₀₁ # W | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # W | ⟨V, S⟩] - d[p.X₀₁ # X₁]))
                + ((d[p.X₀₂ # U | ⟨V, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # U | ⟨W, S⟩] - d[p.X₀₂ # X₂])
                 + (d[p.X₀₂ # V | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # V | ⟨W, S⟩] - d[p.X₀₂ # X₂])
                 + (d[p.X₀₂ # W | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # W | ⟨V, S⟩] - d[p.X₀₂ # X₂])))
    := by
  have hS : Measurable S := ((hX₁.add' hX₂).add' hX₁').add' hX₂'
  have hU : Measurable U := hX₁.add' hX₂
  have hV : Measurable V := hX₁'.add hX₂
  have hW : Measurable W := hX₁'.add hX₁
  have hUVW : U + V + W = 0 := sum_uvw_eq_zero X₁ X₂ X₁'
  have hz (a : ℝ) : a = ∑ z, (ℙ (S ⁻¹' {z})).toReal * a := by
    rw [← Finset.sum_mul, sum_measure_preimage_singleton' ℙ hS, one_mul]
  rw [hz k, hz (d[p.X₀₁ # X₁]), hz (d[p.X₀₂ # X₂])]
  simp only [condMutualInfo_eq_sum' hS, ← Finset.sum_add_distrib, ← mul_add,
    condRuzsaDist'_prod_eq_sum', hU, hS, hV, hW, ← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum,
    ← mul_assoc (p.η/6), mul_comm (p.η/6), mul_assoc _ _ (p.η/6)]
  apply Finset.sum_le_sum (fun i _hi ↦ ?_)
  rcases eq_or_ne (ℙ (S ⁻¹' {i})) 0 with h'i|h'i
  · simp [h'i]
  gcongr
  have : IsProbabilityMeasure (ℙ[|S ⁻¹' {i}]) := cond_isProbabilityMeasure ℙ h'i
  linarith [construct_good_improved'' h_min (ℙ[|S ⁻¹' {i}]) hUVW hU hV hW]

variable (p)

lemma dist_diff_bound_1 :
      (d[p.X₀₁ # U | ⟨V, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # U | ⟨W, S⟩] - d[p.X₀₁ # X₁])
    + (d[p.X₀₁ # V | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # V | ⟨W, S⟩] - d[p.X₀₁ # X₁])
    + (d[p.X₀₁ # W | ⟨U, S⟩] - d[p.X₀₁ # X₁]) + (d[p.X₀₁ # W | ⟨V, S⟩] - d[p.X₀₁ # X₁])
    ≤ (16 * k + 6 * d[X₁ # X₁] + 2 * d[X₂ # X₂]) / 4 + (H[X₁ + X₁'] - H[X₂ + X₂']) / 4
      + (H[X₂ | X₂ + X₂'] - H[X₁ | X₁ + X₁']) / 4 := by
  have I1 := gen_ineq_01 p.X₀₁ p.hmeas1 X₁ X₂ X₂' X₁' hX₁ hX₂ hX₂' hX₁' h_indep.reindex_four_abcd
  have I2 := gen_ineq_00 p.X₀₁ p.hmeas1 X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h_indep.reindex_four_abdc
  have I3 := gen_ineq_10 p.X₀₁ p.hmeas1 X₁ X₂' X₂ X₁' hX₁ hX₂' hX₂ hX₁' h_indep.reindex_four_acbd
  have I4 := gen_ineq_10 p.X₀₁ p.hmeas1 X₁ X₂' X₁' X₂ hX₁ hX₂' hX₁' hX₂ h_indep.reindex_four_acdb
  have I5 := gen_ineq_00 p.X₀₁ p.hmeas1 X₁ X₁' X₂ X₂' hX₁ hX₁' hX₂ hX₂' h_indep.reindex_four_adbc
  have I6 := gen_ineq_01 p.X₀₁ p.hmeas1 X₁ X₁' X₂' X₂ hX₁ hX₁' hX₂' hX₂ h_indep.reindex_four_adcb
  have C1 : U + X₂' + X₁' = S := by abel
  have C2 : W + X₂ + X₂' = S := by abel
  have C3 : X₁ + X₂' + X₂ + X₁' = S := by abel
  have C4 : X₁ + X₂' + X₁' + X₂ = S := by abel
  have C5 : W + X₂' + X₂ = S := by abel
  have C7 : X₂ + X₁' = V := by abel
  have C8 : X₁ + X₁' = W := by abel
  have C9 : d[X₁ # X₂'] = d[X₁ # X₂] :=
    ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
  have C10 : d[X₂ # X₁'] = d[X₁' # X₂] := rdist_symm
  have C11 : d[X₁ # X₁'] = d[X₁ # X₁] :=
    ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₁.symm
  have C12 : d[X₁' # X₂'] = d[X₁ # X₂] :=
    ProbabilityTheory.IdentDistrib.rdist_eq h₁.symm h₂.symm
  have C13 : d[X₂ # X₂'] = d[X₂ # X₂] :=
    ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₂.aemeasurable) h₂.symm
  have C14 : d[X₁' # X₂] = d[X₁ # X₂] :=
    ProbabilityTheory.IdentDistrib.rdist_eq h₁.symm (IdentDistrib.refl hX₂.aemeasurable)
  have C15 : H[X₁' + X₂'] = H[U] := by
    apply ProbabilityTheory.IdentDistrib.entropy_eq
    have I : IdentDistrib (⟨X₁, X₂⟩) (⟨X₁', X₂'⟩) := by
      exact IdentDistrib.prod_mk h₁ h₂ (h_indep.indepFun zero_ne_one)
        (h_indep.indepFun (show 3 ≠ 2 by decide))
    exact I.symm.comp measurable_add
  have C16 : H[X₂'] = H[X₂] := ProbabilityTheory.IdentDistrib.entropy_eq h₂.symm
  have C17 : H[X₁'] = H[X₁] := ProbabilityTheory.IdentDistrib.entropy_eq h₁.symm
  have C18 : d[X₂' # X₁'] = d[X₁' # X₂'] := rdist_symm
  have C19 : H[X₂' + X₁'] = H[U] := by rw [add_comm]; exact C15
  have C20 : d[X₂' # X₂] = d[X₂ # X₂] :=
    ProbabilityTheory.IdentDistrib.rdist_eq h₂.symm (IdentDistrib.refl hX₂.aemeasurable)
  have C21 : H[V] = H[U] := by
    apply ProbabilityTheory.IdentDistrib.entropy_eq
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) := by
      apply IdentDistrib.prod_mk h₁.symm (IdentDistrib.refl hX₂.aemeasurable)
        (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C22 : H[X₁ + X₂'] = H[X₁ + X₂] := by
    apply ProbabilityTheory.IdentDistrib.entropy_eq
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) := by
      apply IdentDistrib.prod_mk (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C23 : X₂' + X₂ = X₂ + X₂' := by abel
  have C24 : H[X₁ | X₁ + X₂'] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁ (hX₁.add' hX₂') hX₁ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prod_mk measurable_add)
  have C25 : H[X₂ | V] = H[X₂ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₂ (hX₁'.add' hX₂) hX₂ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk h₁.symm (IdentDistrib.refl hX₂.aemeasurable)
        (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prod_mk measurable_add)
  have C26 : H[X₂' | X₂' + X₁'] = H[X₂ | X₁ + X₂] := by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁'.add' hX₂') hX₂ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk h₁.symm h₂.symm
        (h_indep.indepFun (show 3 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prod_mk measurable_add)
  have C27 : H[X₂' | X₂ + X₂'] = H[X₂ | X₂ + X₂'] := by
    conv_lhs => rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₂'.add' hX₂) hX₂ (hX₂.add' hX₂')
    have I : IdentDistrib (⟨X₂', X₂⟩) (⟨X₂, X₂'⟩) := by
      exact IdentDistrib.prod_mk h₂.symm h₂
        (h_indep.indepFun (show 2 ≠ 1 by decide)) (h_indep.indepFun (show 1 ≠ 2 by decide))
    exact I.comp (measurable_fst.prod_mk measurable_add)
  have C28 : H[X₁' | X₁' + X₂'] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add' hX₂') hX₁ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk h₁.symm h₂.symm
        (h_indep.indepFun (show 3 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prod_mk measurable_add)
  have C29 : H[X₁' | V] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add' hX₂) hX₁ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk h₁.symm (IdentDistrib.refl hX₂.aemeasurable)
        (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prod_mk measurable_add)
  have C30 : H[X₂ | X₁ + X₂] = H[X₁ | X₁ + X₂] := by
    have := condEntropy_of_injective ℙ hX₁ (hX₁.add' hX₂) _ (fun p ↦ add_right_injective p)
    convert this with ω
    simp [add_comm (X₁ ω), add_assoc (X₂ ω)]
  simp only [C1, C2, C3, C4, C5, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19,
    C20, C21, C22, C23, C24, C25, C26, C27, C28, C29, C30] at I1 I2 I3 I4 I5 I6 ⊢
  linarith only [I1, I2, I3, I4, I5, I6]

lemma dist_diff_bound_2 :
      ((d[p.X₀₂ # U | ⟨V, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # U | ⟨W, S⟩] - d[p.X₀₂ # X₂])
    + (d[p.X₀₂ # V | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # V | ⟨W, S⟩] - d[p.X₀₂ # X₂])
    + (d[p.X₀₂ # W | ⟨U, S⟩] - d[p.X₀₂ # X₂]) + (d[p.X₀₂ # W | ⟨V, S⟩] - d[p.X₀₂ # X₂]))
    ≤ (16 * k + 6 * d[X₂ # X₂] + 2 * d[X₁ # X₁]) / 4 + (H[X₂ + X₂'] - H[X₁ + X₁']) / 4
      + (H[X₁ | X₁ + X₁'] - H[X₂ | X₂ + X₂']) / 4 := by
  have I1 := gen_ineq_01 p.X₀₂ p.hmeas2 X₂ X₁ X₂' X₁' hX₂ hX₁ hX₂' hX₁' h_indep.reindex_four_bacd
  have I2 := gen_ineq_00 p.X₀₂ p.hmeas2 X₂ X₁ X₁' X₂' hX₂ hX₁ hX₁' hX₂' h_indep.reindex_four_badc
  have I3 := gen_ineq_10 p.X₀₂ p.hmeas2 X₂ X₂' X₁ X₁' hX₂ hX₂' hX₁ hX₁' h_indep.reindex_four_bcad
  have I4 := gen_ineq_10 p.X₀₂ p.hmeas2 X₂ X₂' X₁' X₁ hX₂ hX₂' hX₁' hX₁ h_indep.reindex_four_bcda
  have I5 := gen_ineq_00 p.X₀₂ p.hmeas2 X₂ X₁' X₁ X₂' hX₂ hX₁' hX₁ hX₂' h_indep.reindex_four_bdac
  have I6 := gen_ineq_01 p.X₀₂ p.hmeas2 X₂ X₁' X₂' X₁ hX₂ hX₁' hX₂' hX₁ h_indep.reindex_four_bdca
  have C1 : X₂ + X₁ = X₁ + X₂ := by abel
  have C2 : X₁ + X₁' = W := by abel
  have C3 : U + X₂' + X₁' = S := by abel
  have C4 : X₂ + X₁' = V := by abel
  have C5 : X₂ + X₂' + X₁ + X₁' = S := by abel
  have C6 : X₂ + X₂' + X₁' + X₁ = S := by abel
  have C7 : V + X₁ + X₂' = S := by abel
  have C8 : V + X₂' + X₁ = S := by abel
  have C9 : d[X₂ # X₁] = d[X₁ # X₂] := rdist_symm
  have C10 : d[X₁ # X₂'] = d[X₁ # X₂] :=
    ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
  have C11 : d[X₂ # X₁'] = d[X₁ # X₂] := by
    rw [rdist_symm]
    exact ProbabilityTheory.IdentDistrib.rdist_eq h₁.symm (IdentDistrib.refl hX₂.aemeasurable)
  have C12 : d[X₂' # X₁'] = d[X₁' # X₂'] := rdist_symm
  have C13 : d[X₂' # X₁] = d[X₁ # X₂'] := rdist_symm
  have C14 : d[X₁' # X₁] = d[X₁ # X₁'] := rdist_symm
  have C15 : d[X₁' # X₂'] = d[X₁ # X₂] :=
    ProbabilityTheory.IdentDistrib.rdist_eq h₁.symm h₂.symm
  have C16 : H[X₁' + X₂'] = H[X₁ + X₂] := by
    apply ProbabilityTheory.IdentDistrib.entropy_eq
    have I : IdentDistrib (⟨X₁, X₂⟩) (⟨X₁', X₂'⟩) := by
      exact IdentDistrib.prod_mk h₁ h₂ (h_indep.indepFun zero_ne_one)
        (h_indep.indepFun (show 3 ≠ 2 by decide))
    exact I.symm.comp measurable_add
  have C17 : H[X₂' + X₁'] = H[X₁ + X₂] := by rw [add_comm]; exact C16
  have C18 : H[X₁'] = H[X₁] := ProbabilityTheory.IdentDistrib.entropy_eq h₁.symm
  have C19 : H[X₂'] = H[X₂] := ProbabilityTheory.IdentDistrib.entropy_eq h₂.symm
  have C20 : H[X₁ + X₂'] = H[X₁ + X₂] := by
    apply ProbabilityTheory.IdentDistrib.entropy_eq
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) := by
      apply IdentDistrib.prod_mk (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C21 : H[X₁' | W] = H[X₁ | W] := by
    conv_rhs => rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add' hX₁) hX₁ (hX₁.add' hX₁')
    have I : IdentDistrib (⟨X₁', X₁⟩) (⟨X₁, X₁'⟩) := by
      exact IdentDistrib.prod_mk h₁.symm h₁
        (h_indep.indepFun (show 3 ≠ 0 by decide)) (h_indep.indepFun (show 0 ≠ 3 by decide))
    exact I.comp (measurable_fst.prod_mk measurable_add)
  have C22 : H[X₂' | X₂' + X₁] = H[X₂ | X₁ + X₂] := by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁.add' hX₂') hX₂ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prod_mk measurable_add)
  have C23 : H[X₁ | X₁ + X₂'] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁ (hX₁.add' hX₂') hX₁ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prod_mk measurable_add)
  have C24 : H[X₂ | V] = H[X₂ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₂ (hX₁'.add' hX₂) hX₂ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk h₁.symm (IdentDistrib.refl hX₂.aemeasurable)
        (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prod_mk measurable_add)
  have C25 : H[X₂' | X₂' + X₁'] = H[X₂ | X₁ + X₂] := by
    rw [add_comm]
    apply IdentDistrib.condEntropy_eq hX₂' (hX₁'.add' hX₂') hX₂ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk h₁.symm h₂.symm
        (h_indep.indepFun (show 3 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_snd.prod_mk measurable_add)
  have C26 : H[X₁' | X₁' + X₂'] = H[X₁ | X₁ + X₂] := by
    apply IdentDistrib.condEntropy_eq hX₁' (hX₁'.add' hX₂') hX₁ (hX₁.add' hX₂)
    have I : IdentDistrib (⟨X₁', X₂'⟩) (⟨X₁, X₂⟩) := by
      exact IdentDistrib.prod_mk h₁.symm h₂.symm
        (h_indep.indepFun (show 3 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp (measurable_fst.prod_mk measurable_add)
  have C27 : H[X₂ | X₁ + X₂] = H[X₁ | X₁ + X₂] := by
    have := condEntropy_of_injective ℙ hX₁ (hX₁.add' hX₂) _ (fun p ↦ add_right_injective p)
    convert this with ω
    simp [add_comm (X₁ ω), add_assoc (X₂ ω)]
  have C28 : H[V] = H[U] := by
    apply ProbabilityTheory.IdentDistrib.entropy_eq
    have I : IdentDistrib (⟨X₁', X₂⟩) (⟨X₁, X₂⟩) := by
      apply IdentDistrib.prod_mk h₁.symm (IdentDistrib.refl hX₂.aemeasurable)
        (h_indep.indepFun (show 3 ≠ 1 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C29 : H[X₂' + X₁] = H[X₁ + X₂] := by
    rw [add_comm]
    apply ProbabilityTheory.IdentDistrib.entropy_eq
    have I : IdentDistrib (⟨X₁, X₂'⟩) (⟨X₁, X₂⟩) := by
      apply IdentDistrib.prod_mk (IdentDistrib.refl hX₁.aemeasurable) h₂.symm
        (h_indep.indepFun (show 0 ≠ 2 by decide)) (h_indep.indepFun zero_ne_one)
    exact I.comp measurable_add
  have C30 : d[X₁ # X₁'] = d[X₁ # X₁] :=
    ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₁.aemeasurable) h₁.symm
  have C31 : d[X₂ # X₂'] = d[X₂ # X₂] :=
    ProbabilityTheory.IdentDistrib.rdist_eq (IdentDistrib.refl hX₂.aemeasurable) h₂.symm
  simp only [C1, C2, C3, C4, C5, C6, C7, C8, C9, C10, C11, C12, C13, C14, C15, C16, C17, C18, C19,
    C20, C21, C22, C23, C24, C25, C25, C26, C27, C28, C29, C30, C31]
    at I1 I2 I3 I4 I5 I6 ⊢
  linarith only [I1, I2, I3, I4, I5, I6]

lemma averaged_final : k ≤ (6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁))
    + p.η / 6 * (8 * k + 2 * (d[X₁ # X₁] + d[X₂ # X₂])) := by
  apply (averaged_construct_good hX₁ hX₂ hX₁' hX₂' h_min).trans
  have : 0 ≤ p.η := p.hη.le
  have := sum_condMutual_le p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep.reindex_four_abdc h_min
  gcongr ?_ + (p.η / 6) * ?_
  linarith [dist_diff_bound_1 p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep,
    dist_diff_bound_2 p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep]

/-- Suppose $0 < \eta < 1/8$.  Let $X_1, X_2$ be tau-minimizers.  Then $d[X_1;X_2] = 0$. The proof
of this lemma uses copies `X₁', X₂'` already in the context. For a version that does not assume
these are given and constructs them instead, use `tau_strictly_decreases'`.
-/
theorem tau_strictly_decreases_aux' (hp : 8 * p.η < 1) : d[X₁ # X₂] = 0 := by
  have : 0 < p.η := p.hη
  have : k ≤ 8 * p.η * k := by calc
    k ≤ (6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁))
        + p.η / 6 * (8 * k + 2 * (d[X₁ # X₁] + d[X₂ # X₂])) :=
      averaged_final p hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min
    _ ≤ 6 * p.η * k - (1 - 5 * p.η) / (1 - p.η) * (2 * p.η * k - I₁) +
        p.η / 6 * (8 * k + 2 * (2 * (k + (2 * p.η * k - I₁) / (1 - p.η)))) := by
      gcongr
      exact second_estimate_aux p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂
        h_indep.reindex_four_abdc h_min
    _ = 8 * p.η * k - (1 - 5 * p.η - 4/6 * p.η) * (2 * p.η * k - I₁) / (1 - p.η) := by ring
    _ ≤ 8 * p.η * k := by
      simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
      apply div_nonneg _ (by linarith)
      apply mul_nonneg (by linarith) _
      linarith [first_estimate p X₁ X₂ X₁' X₂' hX₁ hX₂ hX₁' hX₂' h₁ h₂ h_indep h_min]
  apply le_antisymm _ (rdist_nonneg hX₁ hX₂)
  nlinarith

theorem tau_strictly_decreases' (hp : 8 * p.η < 1) : d[X₁ # X₂] = 0 := by
  let ⟨A, mA, μ, Y₁, Y₂, Y₁', Y₂', hμ, h_indep, hY₁, hY₂, hY₁', hY₂', h_id1, h_id2, h_id1', h_id2'⟩
    := independent_copies4_nondep hX₁ hX₂ hX₁ hX₂ ℙ ℙ ℙ ℙ
  rw [← h_id1.rdist_eq h_id2]
  letI : MeasureSpace A := ⟨μ⟩
  have : IsProbabilityMeasure (ℙ : Measure A) := hμ
  rw [← h_id1.tau_minimizes p h_id2] at h_min
  exact tau_strictly_decreases_aux' p hY₁ hY₂ hY₁' hY₂' (h_id1.trans h_id1'.symm)
    (h_id2.trans h_id2'.symm) h_indep.reindex_four_abdc h_min hp

end MainEstimates

section EntropicPFR

open MeasureTheory ProbabilityTheory
universe uG

open scoped Topology
open Filter Set

variable {Ω₀₁ Ω₀₂ : Type*} [MeasureSpace Ω₀₁] [MeasureSpace Ω₀₂]
  [IsProbabilityMeasure (ℙ : Measure Ω₀₁)] [IsProbabilityMeasure (ℙ : Measure Ω₀₂)]

variable {G : Type uG} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G] [MeasurableSpace G]
  [MeasurableSingletonClass G]
variable (p : refPackage Ω₀₁ Ω₀₂ G)

/-- For `p.η ≤ 1/8`, there exist τ-minimizers `X₁, X₂` at zero Rusza distance. For `p.η < 1/8`,
all minimizers are fine, by `tau_strictly_decreases'`. For `p.η = 1/8`, we use a limit of
minimizers for `η < 1/8`, which exists by compactness. -/
lemma tau_minimizer_exists_rdist_eq_zero :
    ∃ (Ω : Type uG) (mΩ : MeasureSpace Ω) (X₁ : Ω → G) (X₂ : Ω → G),
      Measurable X₁ ∧ Measurable X₂ ∧ IsProbabilityMeasure (ℙ : Measure Ω) ∧ tau_minimizes p X₁ X₂
      ∧ d[X₁ # X₂] = 0 := by
  -- let `uₙ` be a sequence converging from below to `η`. In particular, `uₙ < 1/8`.
  obtain ⟨u, -, u_mem, u_lim⟩ :
      ∃ u, StrictMono u ∧ (∀ (n : ℕ), u n ∈ Set.Ioo 0 p.η) ∧ Tendsto u atTop (𝓝 p.η) :=
    exists_seq_strictMono_tendsto' p.hη
  -- For each `n`, consider a minimizer associated to `η = uₙ`.
  let q : ℕ → refPackage Ω₀₁ Ω₀₂ G := fun n ↦
    ⟨p.X₀₁, p.X₀₂, p.hmeas1, p.hmeas2, u n, (u_mem n).1, by linarith [(u_mem n).2, p.hη']⟩
  have : ∀ n, ∃ (μ : Measure G × Measure G),
    IsProbabilityMeasure μ.1 ∧ IsProbabilityMeasure μ.2 ∧
      ∀ (ν₁ : Measure G) (ν₂ : Measure G), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      τ[id ; μ.1 # id ; μ.2 | q n] ≤ τ[id ; ν₁ # id ; ν₂ | q n] :=
    fun n ↦ tau_min_exists_measure (q n)
  choose μ μ1_prob μ2_prob hμ using this
  -- The minimizer associated to `uₙ` is at zero Rusza distance of itself, by
  -- lemma `tau_strictly_decreases'`.
  have I n : d[id ; (μ n).1 # id ; (μ n).2] = 0 := by
    let M : MeasureSpace (G × G) := ⟨(μ n).1.prod (μ n).2⟩
    have : IsProbabilityMeasure ((μ n).1.prod (μ n).2) := by infer_instance
    have : d[@Prod.fst G G # @Prod.snd G G] = d[id ; (μ n).1 # id ; (μ n).2] :=
      IdentDistrib.rdist_eq IdentDistrib.fst_id IdentDistrib.snd_id
    rw [← this]
    apply tau_strictly_decreases' (q n) measurable_fst measurable_snd ?_
      (by linarith [(u_mem n).2, p.hη'])
    intro ν₁ ν₂ h₁ h₂
    have A : τ[@Prod.fst G G # @Prod.snd G G | q n] = τ[id ; (μ n).1 # id ; (μ n).2 | q n] :=
      ProbabilityTheory.IdentDistrib.tau_eq (q n) IdentDistrib.fst_id IdentDistrib.snd_id
    rw [A]
    exact hμ n _ _ h₁ h₂
  -- extract a converging subsequence of the sequence of minimizers, seen as pairs of probability
  -- measures on `G` (which is a compact space).
  let μ' : ℕ → ProbabilityMeasure G × ProbabilityMeasure G :=
    fun n ↦ (⟨(μ n).1, μ1_prob n⟩, ⟨(μ n).2, μ2_prob n⟩)
  let _i : TopologicalSpace G := (⊥ : TopologicalSpace G)
  have : DiscreteTopology G := ⟨rfl⟩
  -- The limiting pair of measures will be the desired minimizer.
  rcases IsCompact.tendsto_subseq (x := μ') isCompact_univ (fun n ↦ mem_univ _)
    with ⟨ν, -, φ, φmono, hν⟩
  have φlim : Tendsto φ atTop atTop := φmono.tendsto_atTop
  let M : MeasureSpace (G × G) := ⟨(ν.1 : Measure G).prod ν.2⟩
  have P : IsProbabilityMeasure ((ν.1 : Measure G).prod (ν.2 : Measure G)) := by infer_instance
  refine ⟨G × G, M, Prod.fst, Prod.snd, measurable_fst, measurable_snd, P, ?_, ?_⟩
  -- check that it is indeed a minimizer, as a limit of minimizers.
  · intro ν₁ ν₂ h₁ h₂
    have A : τ[@Prod.fst G G # @Prod.snd G G | p] = τ[id ; ν.1 # id ; ν.2 | p] :=
      ProbabilityTheory.IdentDistrib.tau_eq p IdentDistrib.fst_id IdentDistrib.snd_id
    rw [A]
    have L1 : Tendsto (fun n ↦ τ[id ; (μ (φ n)).1 # id ; (μ (φ n)).2 | q (φ n)]) atTop
        (𝓝 (τ[id ; ν.1 # id ; ν.2 | p])) := by
      apply Tendsto.add (Tendsto.add ?_ (Tendsto.mul (u_lim.comp φlim) ?_))
          (Tendsto.mul (u_lim.comp φlim) ?_)
      · apply Tendsto.comp (continuous_rdist_restrict_probabilityMeasure.tendsto _) hν
      · have : Continuous
          (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ d[p.X₀₁ ; ℙ # id ; μ.1]) :=
        Continuous.comp (continuous_rdist_restrict_probabilityMeasure₁' _ _ p.hmeas1) continuous_fst
        apply Tendsto.comp (this.tendsto _) hν
      · have : Continuous
          (fun (μ : ProbabilityMeasure G × ProbabilityMeasure G) ↦ d[p.X₀₂ ; ℙ # id ; μ.2]) :=
        Continuous.comp (continuous_rdist_restrict_probabilityMeasure₁' _ _ p.hmeas2) continuous_snd
        apply Tendsto.comp (this.tendsto _) hν
    have L2 : Tendsto (fun n ↦ τ[id ; ν₁ # id ; ν₂ | q (φ n)]) atTop
        (𝓝 (τ[id ; ν₁ # id ; ν₂ | p])) :=
      Tendsto.add (Tendsto.add tendsto_const_nhds (Tendsto.mul (u_lim.comp φlim)
        tendsto_const_nhds)) (Tendsto.mul (u_lim.comp φlim) tendsto_const_nhds)
    exact le_of_tendsto_of_tendsto' L1 L2 (fun n ↦ hμ (φ n) _ _ h₁ h₂)
  -- check that it has zero Rusza distance, as a limit of a sequence at zero Rusza distance.
  · have : d[@Prod.fst G G # @Prod.snd G G] = d[id ; ν.1 # id ; ν.2] :=
      IdentDistrib.rdist_eq IdentDistrib.fst_id IdentDistrib.snd_id
    rw [this]
    have L1 : Tendsto (fun n ↦ d[id ; (μ (φ n)).1 # id ; (μ (φ n)).2]) atTop
      (𝓝 (d[id ; ν.1 # id ; (ν.2 : Measure G)])) := by
        apply Tendsto.comp (continuous_rdist_restrict_probabilityMeasure.tendsto _) hν
    have L2 : Tendsto (fun n ↦ d[id ; (μ (φ n)).1 # id ; (μ (φ n)).2]) atTop (𝓝 0) := by simp [I]
    exact tendsto_nhds_unique L1 L2

/-- `entropic_PFR_conjecture_improv`: For two $G$-valued random variables $X^0_1, X^0_2$, there is some
    subgroup $H \leq G$ such that $d[X^0_1;U_H] + d[X^0_2;U_H] \le 10 d[X^0_1;X^0_2]$. -/
theorem entropic_PFR_conjecture_improv (hpη : p.η = 1/8) :
    ∃ H : AddSubgroup G, ∃ Ω : Type uG, ∃ mΩ : MeasureSpace Ω, ∃ U : Ω → G,
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧
    IsUniform H U ∧ d[p.X₀₁ # U] + d[p.X₀₂ # U] ≤ 10 * d[p.X₀₁ # p.X₀₂] := by
  obtain ⟨Ω', mΩ', X₁, X₂, hX₁, hX₂, hP, htau_min, hdist⟩ := tau_minimizer_exists_rdist_eq_zero p
  obtain ⟨H, U, hU, hH_unif, hdistX₁, hdistX₂⟩ := exists_isUniform_of_rdist_eq_zero hX₁ hX₂ hdist
  refine ⟨H, Ω', inferInstance, U, inferInstance, hU, hH_unif , ?_⟩
  have h : τ[X₁ # X₂ | p] ≤ τ[p.X₀₂ # p.X₀₁ | p] := is_tau_min p htau_min p.hmeas2 p.hmeas1
  rw [tau, tau, hpη] at h
  norm_num at h
  have : d[p.X₀₁ # p.X₀₂] = d[p.X₀₂ # p.X₀₁] := rdist_symm
  have : d[p.X₀₁ # U] ≤ d[p.X₀₁ # X₁] + d[X₁ # U] := rdist_triangle p.hmeas1 hX₁ hU
  have : d[p.X₀₂ # U] ≤ d[p.X₀₂ # X₂] + d[X₂ # U] := rdist_triangle p.hmeas2 hX₂ hU
  linarith

end EntropicPFR

section PFR

/- In this file the power notation will always mean the base and exponent are real numbers. -/
local macro_rules | `($x ^ $y) => `(HPow.hPow ($x : ℝ) ($y : ℝ))

open Pointwise Set MeasureTheory ProbabilityTheory Real Fintype Function

variable {G Ω : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2] [Fintype G]
    {A B : Set G} {K : ℝ}

/-- Auxiliary statement towards the polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of
an elementary abelian 2-group of doubling constant at most $K$, then there exists a subgroup $H$
such that $A$ can be covered by at most $K^6 |A|^{1/2} / |H|^{1/2}$ cosets of $H$, and $H$ has
the same cardinality as $A$ up to a multiplicative factor $K^10$. -/
lemma PFR_conjecture_improv_aux (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ 6 * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card H ≤ K ^ 10 * Nat.card A ∧ Nat.card A ≤ K ^ 10 * Nat.card H ∧ A ⊆ c + H := by
  classical
  let mG : MeasurableSpace G := ⊤
  have : MeasurableSingletonClass G := ⟨λ _ ↦ trivial⟩
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
  rcases exists_isUniform_measureSpace A h₀A with ⟨Ω₀, mΩ₀, UA, hP₀, UAmeas, UAunif, -⟩
  have : d[UA # UA] ≤ log K := rdist_le_of_isUniform_of_card_add_le h₀A hA UAunif UAmeas
  let p : refPackage Ω₀ Ω₀ G := ⟨UA, UA, UAmeas, UAmeas, 1/8, (by norm_num), (by norm_num)⟩
  -- entropic PFR gives a subgroup `H` which is close to `A` for the Rusza distance
  rcases entropic_PFR_conjecture_improv p (by norm_num)
    with ⟨H, Ω₁, mΩ₁, UH, hP₁, UHmeas, UHunif, hUH⟩
  rcases independent_copies_two UAmeas UHmeas
    with ⟨Ω, mΩ, VA, VH, hP, VAmeas, VHmeas, Vindep, idVA, idVH⟩
  have VAunif : IsUniform A VA := UAunif.of_identDistrib idVA.symm $ measurableSet_discrete _
  have VHunif : IsUniform H VH := UHunif.of_identDistrib idVH.symm $ measurableSet_discrete _
  have : d[VA # VH] ≤ 10/2 * log K := by rw [idVA.rdist_eq idVH]; linarith
  have H_pos : (0 : ℝ) < Nat.card (H : Set G) := by
    have : 0 < Nat.card (H : Set G) := Nat.card_pos
    positivity
  have Icard : |log (Nat.card A) - log (Nat.card (H : Set G))| ≤ 10 * log K := by
    rw [← VAunif.entropy_eq VAmeas, ← VHunif.entropy_eq VHmeas]
    apply (diff_ent_le_rdist VAmeas VHmeas).trans
    linarith
  have IAH : Nat.card A ≤ K ^ 10 * Nat.card (H : Set G) := by
    have : log (Nat.card A) ≤ log K * 10 + log (Nat.card (H : Set G)) := by
      linarith [(le_abs_self _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log A_pos).symm
    · rw [exp_add, exp_log H_pos, ← rpow_def_of_pos K_pos]
  have IHA : Nat.card (H : Set G) ≤ K ^ 10 * Nat.card A := by
    have : log (Nat.card (H : Set G)) ≤ log K * 10 + log (Nat.card A) := by
      linarith [(neg_le_abs_self _).trans Icard]
    convert exp_monotone this using 1
    · exact (exp_log H_pos).symm
    · rw [exp_add, exp_log A_pos, ← rpow_def_of_pos K_pos]
  -- entropic PFR shows that the entropy of `VA - VH` is small
  have I : log K * (-10/2) + log (Nat.card A) * (-1/2) + log (Nat.card (H : Set G)) * (-1/2)
      ≤ - H[VA - VH] := by
    rw [Vindep.rdist_eq VAmeas VHmeas] at this
    have : H[VA] = log (Nat.card A) := VAunif.entropy_eq VAmeas
    have : H[VH] = log (Nat.card (H : Set G)) := VHunif.entropy_eq VHmeas
    linarith
  -- therefore, there exists a point `x₀` which is attained by `VA - VH` with a large probability
  obtain ⟨x₀, h₀⟩ : ∃ x₀ : G, rexp (- H[VA - VH]) ≤ (ℙ : Measure Ω).real ((VA - VH) ⁻¹' {x₀}) :=
    prob_ge_exp_neg_entropy' _ ((VAmeas.sub VHmeas).comp measurable_id')
  -- massage the previous inequality to get that `A ∩ (H + {x₀})` is large
  have J : K ^ (-10/2) * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (1/2) ≤
      Nat.card (A ∩ (H + {x₀}) : Set G) := by
    rw [VAunif.measureReal_preimage_sub VAmeas VHunif VHmeas Vindep] at h₀
    have := (Real.exp_monotone I).trans h₀
    rw [le_div_iff (by positivity)] at this
    convert this using 1
    rw [exp_add, exp_add, ← rpow_def_of_pos K_pos, ← rpow_def_of_pos A_pos, ← rpow_def_of_pos H_pos]
    rpow_ring
    norm_num
  have Hne : Set.Nonempty (A ∩ (H + {x₀} : Set G)) := by
    by_contra h'
    have : (0 : ℝ) < Nat.card (A ∩ (H + {x₀}) : Set G) := lt_of_lt_of_le (by positivity) J
    simp only [Nat.card_eq_fintype_card, card_of_isEmpty, CharP.cast_eq_zero, lt_self_iff_false,
      not_nonempty_iff_eq_empty.1 h'] at this
  /- use Rusza covering lemma to cover `A` by few translates of `A ∩ (H + {x₀}) - A ∩ (H + {x₀})`
  (which is contained in `H`). The number of translates is at most
  `#(A + (A ∩ (H + {x₀}))) / #(A ∩ (H + {x₀}))`, where the numerator is controlled as this is
  a subset of `A + A`, and the denominator is bounded below by the previous inequality`. -/
  rcases Set.exists_subset_add_sub (toFinite A) (toFinite (A ∩ ((H + {x₀} : Set G)))) Hne with
    ⟨u, hu, Au, -⟩
  have Iu : Nat.card u ≤ K ^ 6 * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2) := by
    have : (0 : ℝ) ≤ Nat.card u := by simp
    have Z1 := mul_le_mul_of_nonneg_left J this
    have Z2 : (Nat.card u * Nat.card (A ∩ (H + {x₀}) : Set G) : ℝ)
      ≤ Nat.card (A + A ∩ (↑H + {x₀})) := by norm_cast
    have Z3 : (Nat.card (A + A ∩ (↑H + {x₀})) : ℝ) ≤ K * Nat.card A := by
      apply le_trans _ hA
      simp only [Nat.cast_le]
      apply Nat.card_mono (toFinite _)
      apply add_subset_add_left (inter_subset_left _ _)
    have : 0 ≤ K ^ (10/2) * Nat.card A ^ (-1/2) * Nat.card (H : Set G) ^ (-1/2) := by positivity
    have T := mul_le_mul_of_nonneg_left ((Z1.trans Z2).trans Z3) this
    convert T using 1 <;> rpow_ring <;> norm_num
  have A_subset_uH : A ⊆ u + H := by
    apply Au.trans
    rw [add_sub_assoc]
    apply add_subset_add_left
    apply (sub_subset_sub (inter_subset_right _ _) (inter_subset_right _ _)).trans
    rintro - ⟨-, -, ⟨y, xy, hy, hxy, rfl⟩, ⟨z, xz, hz, hxz, rfl⟩, rfl⟩
    simp only [mem_singleton_iff] at hxy hxz
    simpa [hxy, hxz, -ElementaryAddCommGroup.sub_eq_add] using H.sub_mem hy hz
  exact ⟨H, u, Iu, IHA, IAH, A_subset_uH⟩

/-- The polynomial Freiman-Ruzsa (PFR) conjecture: if $A$ is a subset of an elementary abelian
2-group of doubling constant at most $K$, then $A$ can be covered by at most $2K^11$ cosets of
a subgroup of cardinality at most $|A|$. -/
theorem PFR_conjecture_improv (h₀A : A.Nonempty) (hA : Nat.card (A + A) ≤ K * Nat.card A) :
     ∃ (H : AddSubgroup G) (c : Set G),
      Nat.card c < 2 * K ^ 11 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  obtain ⟨A_pos, -, K_pos⟩ : (0 : ℝ) < Nat.card A ∧ (0 : ℝ) < Nat.card (A + A) ∧ 0 < K :=
    PFR_conjecture_pos_aux h₀A hA
  -- consider the subgroup `H` given by Lemma `PFR_conjecture_aux`.
  obtain ⟨H, c, hc, IHA, IAH, A_subs_cH⟩ : ∃ (H : AddSubgroup G) (c : Set G),
    Nat.card c ≤ K ^ 6 * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2)
      ∧ Nat.card (H : Set G) ≤ K ^ 10 * Nat.card A ∧ Nat.card A ≤ K ^ 10 * Nat.card (H : Set G)
      ∧ A ⊆ c + H :=
    PFR_conjecture_improv_aux h₀A hA
  have H_pos : (0 : ℝ) < Nat.card (H : Set G) := by
    have : 0 < Nat.card (H : Set G) := Nat.card_pos; positivity
  rcases le_or_lt (Nat.card (H : Set G)) (Nat.card A) with h|h
  -- If `#H ≤ #A`, then `H` satisfies the conclusion of the theorem
  · refine ⟨H, c, ?_, h, A_subs_cH⟩
    calc
    Nat.card c ≤ K ^ 6 * (Nat.card A) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2) := hc
    _ ≤ K ^ 6 * (K ^ 10 * Nat.card (H : Set G)) ^ (1/2) * (Nat.card (H : Set G)) ^ (-1/2) := by
      gcongr
    _ = K ^ 11 := by rpow_ring; norm_num
    _ < 2 * K ^ 11 := by linarith [show 0 < K ^ 11 by positivity]
  -- otherwise, we decompose `H` into cosets of one of its subgroups `H'`, chosen so that
  -- `#A / 2 < #H' ≤ #A`. This `H'` satisfies the desired conclusion.
  · obtain ⟨H', IH'A, IAH', H'H⟩ : ∃ H' : AddSubgroup G, Nat.card (H' : Set G) ≤ Nat.card A
          ∧ Nat.card A < 2 * Nat.card (H' : Set G) ∧ H' ≤ H := by
      have A_pos' : 0 < Nat.card A := by exact_mod_cast A_pos
      exact ElementaryAddCommGroup.exists_subgroup_subset_card_le H h.le A_pos'.ne'
    have : (Nat.card A / 2 : ℝ) < Nat.card (H' : Set G) := by
      rw [div_lt_iff zero_lt_two, mul_comm]; norm_cast
    have H'_pos : (0 : ℝ) < Nat.card (H' : Set G) := by
      have : 0 < Nat.card (H' : Set G) := Nat.card_pos; positivity
    obtain ⟨u, HH'u, hu⟩ := AddSubgroup.exists_left_transversal_of_le H'H
    refine ⟨H', c + u, ?_, IH'A, by rwa [add_assoc, HH'u]⟩
    calc
    (Nat.card (c + u) : ℝ)
      ≤ Nat.card c * Nat.card u := mod_cast card_add_le
    _ ≤ (K ^ 6 * (Nat.card A) ^ (1 / 2) * (Nat.card (H : Set G) ^ (-1 / 2)))
          * (Nat.card (H : Set G) / Nat.card (H' : Set G)) := by
        gcongr
        apply le_of_eq
        rw [eq_div_iff H'_pos.ne']
        norm_cast
    _ < (K ^ 6 * (Nat.card A) ^ (1 / 2) * (Nat.card (H : Set G) ^ (-1 / 2)))
          * (Nat.card (H : Set G) / (Nat.card A / 2)) := by
        gcongr
    _ = 2 * K ^ 6 * (Nat.card A) ^ (-1/2) * (Nat.card (H : Set G)) ^ (1/2) := by
        have : (0 : ℝ) < Nat.card H := H_pos
        field_simp
        rpow_ring
        norm_num
    _ ≤ 2 * K ^ 6 * (Nat.card A) ^ (-1/2) * (K ^ 10 * Nat.card A) ^ (1/2) := by
        gcongr
    _ = 2 * K ^ 11 := by
        rpow_ring
        norm_num

/-- Corollary of `PFR_conjecture_improv` in which the ambient group is not required to be finite
(but) then $H$ and $c$ are finite. -/
theorem PFR_conjecture_improv' {G : Type*} [AddCommGroup G] [ElementaryAddCommGroup G 2]
    {A : Set G} {K : ℝ} (h₀A : A.Nonempty) (Afin : A.Finite)
    (hA : Nat.card (A + A) ≤ K * Nat.card A) :
    ∃ (H : AddSubgroup G) (c : Set G), c.Finite ∧ (H : Set G).Finite ∧
      Nat.card c < 2 * K ^ 11 ∧ Nat.card H ≤ Nat.card A ∧ A ⊆ c + H := by
  let G' := AddSubgroup.closure A
  let G'fin : Fintype G' := by
    exact Finite.fintype (ElementaryAddCommGroup.finite_closure Afin)
  have G'Elem : ElementaryAddCommGroup G' 2 := ElementaryAddCommGroup.subgroup _
  let ι : G'→+ G := G'.subtype
  have ι_inj : Injective ι := AddSubgroup.subtype_injective G'
  let A' : Set G' := ι ⁻¹' A
  have A_rg : A ⊆ range ι := by simpa using AddSubgroup.subset_closure
  have cardA' : Nat.card A' = Nat.card A := Nat.card_preimage_of_injective ι_inj A_rg
  have hA' : Nat.card (A' + A') ≤ K * Nat.card A' := by
    rwa [cardA', preimage_add_preimage ι_inj A_rg A_rg,
         Nat.card_preimage_of_injective ι_inj (add_subset_range A_rg A_rg)]
  rcases PFR_conjecture_improv (h₀A.preimage' A_rg) hA' with ⟨H', c', hc', hH', hH'₂⟩
  refine ⟨AddSubgroup.map ι H', ι '' c', toFinite _, toFinite (ι '' H'), ?_, ?_, fun x hx ↦ ?_⟩
  · rwa [Nat.card_image_of_injective ι_inj]
  · erw [Nat.card_image_of_injective ι_inj, ← cardA']
    exact hH'
  · erw [← image_add]
    exact ⟨⟨x, AddSubgroup.subset_closure hx⟩, hH'₂ hx, rfl⟩

end PFR
