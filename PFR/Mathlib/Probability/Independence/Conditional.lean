import PFR.ForMathlib.Pair
import PFR.Mathlib.Data.Set.Image
import PFR.Mathlib.MeasureTheory.MeasurableSpace.Defs
import PFR.Mathlib.MeasureTheory.Measure.Dirac
import PFR.Mathlib.MeasureTheory.Measure.Typeclasses
import PFR.Mathlib.Probability.ConditionalProbability
import PFR.Mathlib.Probability.IdentDistrib
import PFR.Tactic.Finiteness

open MeasureTheory Measure Set
open scoped BigOperators

namespace ProbabilityTheory
section defs
variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {h : Ω → γ}

/-- The assertion that `f` and `g` are conditionally independent relative to `h`. -/
def CondIndepFun (f : Ω → α) (g : Ω → β) (h : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ z ∂ (μ.map h), IndepFun f g (μ[|h ← z])

lemma condIndepFun_iff : CondIndepFun f g h μ ↔ ∀ᵐ z ∂ (μ.map h), IndepFun f g (μ[|h ← z]) := by rfl

variable [MeasurableSingletonClass γ]

/-- Composing independent functions with a measurable embedding of conull range gives independent
functions. -/
lemma CondIndepFun.comp_right {i : Ω' → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hfg : CondIndepFun f g h μ) :
    CondIndepFun (f ∘ i) (g ∘ i) (h ∘ i) (μ.comap i) := by
  rw [condIndepFun_iff] at hfg ⊢
  rw [←Measure.map_map hh hi.measurable, hi.map_comap, restrict_eq_self_of_ae_mem hi']
  refine hfg.mono $ fun c hc ↦ ?_
  rw [preimage_comp, ←comap_cond hi hi' $ hh $ measurableSet_singleton _]
  exact IndepFun.comp_right hi (cond_absolutelyContinuous.ae_le hi') hf hg hc

end defs

section copy
universe u
variable {Ω : Type*} {α β : Type u} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [Fintype β]

open Function Set Measure

/-- For $X, Y$ random variables, there exist conditionally independent trials $X_1, X_2, Y'$. -/
lemma condIndep_copies (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω' → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib (⟨X₁, Y'⟩) (⟨X, Y⟩) ν μ ∧
      IdentDistrib (⟨X₂, Y'⟩) (⟨X, Y⟩) ν μ := by
  let m' := fun (y : β) ↦ ((μ[|Y ← y]).map X)
  let m := fun (y : β) ↦ ((m' y).prod (m' y)).prod (Measure.dirac y)
  let ν : Measure ((α × α) × β) := ∑ y : β, ((μ (Y ⁻¹' {y})) • (m y))

  have h3' (y : β) : { ω : Ω | Y ω = y } ∈ ae (μ[|Y ← y]) := by
    rw [mem_ae_iff, ← cond_inter_self]
    . have : (Y ⁻¹' {y}) ∩ { ω : Ω | Y ω = y }ᶜ = ∅ := by
        ext _; simp
      simp [this]
    exact hY $ measurableSet_discrete _

  have h3 (y : β) : IdentDistrib (fun ω ↦ (X ω, y)) (⟨X, Y⟩) (μ[|Y ← y]) (μ[|Y ← y]) := by
    apply IdentDistrib.of_ae_eq (hX.prod_mk measurable_const).aemeasurable
    apply Filter.eventuallyEq_of_mem (h3' y)
    intro ω; simp; exact fun a ↦ id a.symm

  have h4 (y : β) : { ω : (α × α) × β| ω.2 = y } ∈ ae (m y) := by
    rw [mem_ae_iff]
    have : { ω : (α × α) × β | ω.2 = y}ᶜ = Prod.snd⁻¹' {t : β | t ≠ y} := by simp; rfl
    rw [this, ← Measure.map_apply measurable_snd]
    all_goals {simp}

  have h5 {y : β} (hy : μ (Y ⁻¹' {y}) ≠ 0) : IsProbabilityMeasure (m' y) := by
    have : IsProbabilityMeasure (μ[|Y ← y]) := cond_isProbabilityMeasure μ hy
    exact isProbabilityMeasure_map hX.aemeasurable

  refine ⟨(α × α) × β, by infer_instance, fun ω ↦ ω.1.1, fun ω ↦ ω.1.2, fun ω ↦ ω.2, ν, ?_, measurable_fst.comp measurable_fst, measurable_snd.comp measurable_fst, measurable_snd, ?_, ?_, ?_⟩
  . constructor
    simp
    have : ∑ y : β, μ (Y ⁻¹' {y})*1 = 1 := by
      simp
      rw [sum_measure_preimage_singleton] <;>
        simp [hY $ measurableSet_discrete _, measure_ne_top]
    rw [← this]
    congr with y
    rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
    . simp [hy]
    congr 1
    have : IsProbabilityMeasure (m' y) := h5 hy
    simp
  . rw [condIndepFun_iff, ae_iff_of_fintype]
    have h1 : ν.map Prod.snd = μ.map Y := by
      rw [law_of_total_probability hY μ, ← Measure.mapₗ_apply_of_measurable measurable_snd, ← Measure.mapₗ_apply_of_measurable hY]
      simp
      congr with y
      rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
      . simp [hy]
      have h6 : IsProbabilityMeasure (m' y) := h5 hy
      have h7 : IsProbabilityMeasure (μ[|Y ← y]) := cond_isProbabilityMeasure μ hy
      congr 3
      rw [Measure.mapₗ_apply_of_measurable measurable_snd, Measure.mapₗ_apply_of_measurable hY]
      simp
      have := (μ[|Y ← y]).map_const y
      simp at this; rw [← this]
      apply Measure.map_congr
      apply Filter.eventuallyEq_of_mem (h3' y)
      intro ω; simp; exact fun a ↦ id a.symm
    intro y hy
    have hy' : ν (Prod.snd⁻¹' {y}) = μ (Y ⁻¹' {y}) := by
      rw [← map_apply measurable_snd (by simp), ← map_apply hY $ measurableSet_discrete _, h1]
    rw [h1] at hy
    have hy'' : μ (Y ⁻¹' {y}) ≠ 0 := by
      convert hy
      exact (map_apply hY $ measurableSet_discrete _).symm

    have h2 : ν[| Prod.snd⁻¹' {y}] = m y := by
      rw [Measure.ext_iff]
      intro E _
      rw [cond_apply ν (measurable_snd (by simp)) E, hy']
      simp
      have h3 : (m y) ((Prod.snd⁻¹' {y}) ∩ E) = (m y) E := by
        apply measure_congr
        apply inter_ae_eq_right_of_ae_eq_univ
        simp
        rw [(show (Prod.snd⁻¹' {y})ᶜ = Prod.snd⁻¹' ({y}ᶜ) by rfl), ← map_apply measurable_snd (by simp)]
        simp
      have h3' {x : β} (hx : x ≠ y) : (m x) ((Prod.snd⁻¹' {y}) ∩ E) = 0 := by
        apply measure_inter_null_of_null_left E
        rw [← Measure.map_apply measurable_snd (by simp), MeasureTheory.Measure.map_snd_prod]
        simp; right; exact hx
      rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
      . rw [h3, ← mul_assoc, ENNReal.inv_mul_cancel hy'', one_mul]
        finiteness
      intro x _ hx
      rw [h3' hx]
      simp
    rw [h2, indepFun_iff_map_prod_eq_prod_map_map]
    . let f : (α × α) × β → α × α := Prod.fst
      show ((m y).map f) = ((m y).map (Prod.fst ∘ f)).prod ((m y).map (Prod.snd ∘ f))
      have : IsProbabilityMeasure (m' y) := h5 hy''
      have : (m y).map f = (m' y).prod (m' y) := by simp
      rw [← map_map measurable_fst measurable_fst, ← map_map measurable_snd measurable_fst, this]
      simp
    . exact (measurable_fst.comp measurable_fst).aemeasurable
    exact (measurable_snd.comp measurable_fst).aemeasurable
  . rw [law_of_total_probability hY μ]
    apply identDistrib_of_sum ((measurable_fst.comp measurable_fst).prod_mk measurable_snd) (hX.prod_mk hY)
    intro y hy
    have h1 : IdentDistrib (fun ω ↦ (ω.1.1, ω.2)) (fun ω ↦ (ω.1.1, y)) (m y) (m y) := by
      apply IdentDistrib.of_ae_eq ((measurable_fst.comp measurable_fst).prod_mk measurable_snd).aemeasurable
      apply Filter.eventuallyEq_of_mem (h4 y)
      intro _; simp
    have h2 : IdentDistrib (fun ω ↦ (ω.1.1, y)) (fun ω ↦ (X ω, y)) (m y) (μ[|Y ← y]) := by
      let f := fun (x : α) ↦ (x, y)
      show IdentDistrib (f ∘ (Prod.fst ∘ Prod.fst)) (f ∘ X) (m y) (μ[|Y ← y])
      apply IdentDistrib.comp _ measurable_prod_mk_right
      apply (identDistrib_comp_fst measurable_fst _ _).trans
      have : IsProbabilityMeasure ((μ[|Y ← y]).map X) := h5 hy
      apply (identDistrib_comp_fst measurable_id _ _).trans
      apply identDistrib_map hX measurable_id
    exact (h1.trans h2).trans (h3 y)
  rw [law_of_total_probability hY μ]
  apply identDistrib_of_sum ((measurable_snd.comp measurable_fst).prod_mk measurable_snd) (hX.prod_mk hY)
  intro y hy
  have h1 : IdentDistrib (fun ω ↦ (ω.1.2, ω.2)) (fun ω ↦ (ω.1.2, y)) (m y) (m y) := by
    apply IdentDistrib.of_ae_eq ((measurable_snd.comp measurable_fst).prod_mk measurable_snd).aemeasurable
    apply Filter.eventuallyEq_of_mem (h4 y)
    intro _; simp
  have h2 : IdentDistrib (fun ω ↦ (ω.1.2, y)) (fun ω ↦ (X ω, y)) (m y) (μ[|Y ← y]) := by
    let f := fun (x : α) ↦ (x, y)
    show IdentDistrib (f ∘ (Prod.snd ∘ Prod.fst)) (f ∘ X) (m y) (μ[|Y ← y])
    apply IdentDistrib.comp _ measurable_prod_mk_right
    apply (identDistrib_comp_fst measurable_snd _ _).trans
    have : IsProbabilityMeasure ((μ[|Y ← y]).map X) := h5 hy
    apply (identDistrib_comp_snd measurable_id _ _).trans
    apply identDistrib_map hX measurable_id
  exact (h1.trans h2).trans (h3 y)

/-- For $X, Y$ random variables, there exist conditionally independent trials $X_1, X_2, Y'$. -/
lemma condIndep_copies' (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : α → β → Prop) (hp : Measurable (uncurry p))
    (hp' : ∀ᵐ ω ∂μ, p (X ω) (Y ω)) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω' → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib (⟨X₁, Y'⟩) (⟨X, Y⟩) ν μ ∧
       IdentDistrib (⟨X₂, Y'⟩) (⟨X, Y⟩) ν μ ∧ (∀ ω, p (X₁ ω) (Y' ω)) ∧ (∀ ω, p (X₂ ω) (Y' ω)) := by
  obtain ⟨Ω', _, X₁, X₂, Y', ν, _, hX₁, hX₂, hY', hXY, hXY₁, hXY₂⟩ :=
    condIndep_copies X Y hX hY μ
  let i := Subtype.val (p := fun ω ↦ p (X₁ ω) (Y' ω) ∧ p (X₂ ω) (Y' ω))
  have hi : MeasurableEmbedding i := MeasurableEmbedding.subtype_coe
    ((hp.comp $ hX₁.prod_mk hY').and $ hp.comp $ hX₂.prod_mk hY').setOf
  have hi' : ∀ᵐ ω ∂ν, ω ∈ range i
  · simp only [mem_setOf_eq, Subtype.range_coe_subtype, Filter.eventually_and]
    exact ⟨hXY₁.symm.ae_snd (p := uncurry p) hp.setOf hp',
      hXY₂.symm.ae_snd (p := uncurry p) hp.setOf hp'⟩
  refine ⟨{ω // p (X₁ ω) (Y' ω) ∧ p (X₂ ω) (Y' ω)}, inferInstance, X₁ ∘ (↑), X₂ ∘ (↑), Y' ∘ (↑),
    ν.comap (↑), ?_, hX₁.comp measurable_subtype_coe, hX₂.comp measurable_subtype_coe,
    hY'.comp measurable_subtype_coe, ?_, ?_, ?_, fun ω ↦ ω.2.1, fun ω ↦ ω.2.2⟩
  · exact hi.isProbabilityMeasure_comap hi'
  · exact hXY.comp_right hi hi' hX₁ hX₂ hY'
  · exact hXY₁.comp_left hi hi' $ hX₁.prod_mk hY'
  · exact hXY₂.comp_left hi hi' $ hX₂.prod_mk hY'

end copy
