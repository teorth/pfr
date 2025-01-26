import PFR.Mathlib.Probability.IdentDistrib
import PFR.ForMathlib.FiniteRange.Defs

-- TODO: Change `ae_snd` to assume `Measurable p`

noncomputable section

open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal

namespace ProbabilityTheory
section IdentDistrib
universe u u' v
variable {Ω Ω' α ι β β' T : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω → β}
  {f' g' : Ω' → β}

/-- If `X` has identical distribution to `X₀`, and `X₀` has finite range, then `X` is almost everywhere equivalent to a random variable of finite range. -/
lemma identDistrib_of_finiteRange {Ω Ω₀ S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace S] [MeasurableSingletonClass S]
    [hS: Nonempty S] {μ: Measure Ω} {μ₀: Measure Ω₀} {X₀: Ω₀ → S} [FiniteRange X₀] {X : Ω → S}
    (hX : Measurable X) (hi : IdentDistrib X₀ X μ₀ μ) :
    ∃ X' : Ω → S, Measurable X' ∧ FiniteRange X' ∧ X' =ᵐ[μ] X := by
  set A := FiniteRange.toFinset X₀
  classical
  let X' (ω : Ω) : S := if (X ω ∈ A) then X ω else hS.some
  use X'
  constructor
  · exact Measurable.ite (MeasurableSet.preimage (Finset.measurableSet A) hX) hX measurable_const
  constructor
  · apply finiteRange_of_finset X' (A ∪ {hS.some})
    intro ω
    simp
    by_cases h: X ω ∈ A
    · left; simp at h; simp [X', h]
    · right
      simp only [ite_eq_right_iff, X']
      exact fun h' ↦ absurd h' h
  apply Filter.eventuallyEq_of_mem (s := X ⁻¹' A)
  · simp [ae]
    rw [← Set.preimage_compl, ← IdentDistrib.measure_preimage_eq hi]
    · convert measure_empty (μ := μ₀)
      ext ω
      simp [A]
    measurability
  intro ω
  simp only [mem_preimage, Finset.mem_coe, ite_eq_left_iff, X']
  tauto

/-- A version of `independent_copies` that guarantees that the copies have `FiniteRange` if the original variables do. -/
lemma independent_copies_finiteRange {X : Ω → α} {Y : Ω' → β}
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    ∃ ν : Measure (α × β), ∃ X' : α × β → α, ∃
    Y' : α × β → β, IsProbabilityMeasure ν
      ∧ Measurable X' ∧ Measurable Y' ∧ IndepFun X' Y' ν
      ∧ IdentDistrib X' X ν μ ∧ IdentDistrib Y' Y ν μ' ∧ FiniteRange X' ∧ FiniteRange Y' := by
  have : Nonempty α := μ.nonempty_of_neZero.map X
  have : Nonempty β := μ'.nonempty_of_neZero.map Y
  obtain ⟨ν, X', Y', hν, hX', hY', hind, hIdX, hIdY⟩ := independent_copies hX hY μ μ'
  rcases identDistrib_of_finiteRange hX' hIdX.symm with ⟨X'', hX'', hX''_finite, hX''_eq⟩
  rcases identDistrib_of_finiteRange hY' hIdY.symm with ⟨Y'', hY'', hY''_finite, hY''_eq⟩
  use ν, X'', Y''
  refine ⟨hν, hX'', hY'', ?_, ?_, ?_, hX''_finite, hY''_finite⟩
  · exact hind.ae_eq hX''_eq.symm hY''_eq.symm
  · convert IdentDistrib.trans _ hIdX
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX'') hX''_eq
  · convert IdentDistrib.trans _ hIdY
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hY'') hY''_eq

/-- A version of `independent_copies3_nondep` that guarantees that the copies have `FiniteRange`
if the original variables do. -/
lemma independent_copies3_nondep_finiteRange {α : Type u}
    [mS : MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃)
    [FiniteRange X₁] [FiniteRange X₂] [FiniteRange X₃]
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂]
    [hμ₃ : IsProbabilityMeasure μ₃] :
    ∃ (A : Type (max u_1 u_2 u_3)) (_ : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' : A → α),
    IsProbabilityMeasure μA ∧
    iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧
      IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃ ∧
      FiniteRange X₁' ∧ FiniteRange X₂' ∧ FiniteRange X₃' := by
    have : Nonempty α := μ₁.nonempty_of_neZero.map X₁
    obtain ⟨A, mA, μA, X₁', X₂', X₃', hμA, hind, hX₁, hX₂, hX₃, hId₁, hId₂, hId₃⟩ :=
      independent_copies3_nondep hX₁ hX₂ hX₃ μ₁ μ₂ μ₃
    rcases identDistrib_of_finiteRange hX₁ hId₁.symm with ⟨X₁'', hX₁'', hX₁''_finite, hX₁''_eq⟩
    rcases identDistrib_of_finiteRange hX₂ hId₂.symm with ⟨X₂'', hX₂'', hX₂''_finite, hX₂''_eq⟩
    rcases identDistrib_of_finiteRange hX₃ hId₃.symm with ⟨X₃'', hX₃'', hX₃''_finite, hX₃''_eq⟩
    use A, mA, μA, X₁'', X₂'', X₃''
    refine ⟨hμA, ?_, hX₁'', hX₂'', hX₃'', ?_, ?_, ?_, hX₁''_finite, hX₂''_finite, hX₃''_finite⟩
    · apply iIndepFun.ae_eq hind
      intro i; fin_cases i
      all_goals simp [hX₁''_eq.symm, hX₂''_eq.symm, hX₃''_eq.symm]
    · convert IdentDistrib.trans _ hId₁
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₁'') hX₁''_eq
    · convert IdentDistrib.trans _ hId₂
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₂'') hX₂''_eq
    convert IdentDistrib.trans _ hId₃
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₃'') hX₃''_eq

/-- A version of `independent_copies4_nondep` that guarantees that the copies have `FiniteRange`
if the original variables do. -/
lemma independent_copies4_nondep_finiteRange {α : Type u}
    [mS : MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3} {Ω₄ : Type u_4}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] [MeasurableSpace Ω₄]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α} {X₄ : Ω₄ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃) (hX₄ : Measurable X₄)
    [FiniteRange X₁] [FiniteRange X₂] [FiniteRange X₃] [FiniteRange X₄]
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃) (μ₄ : Measure Ω₄)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂] [hμ₃ : IsProbabilityMeasure μ₃]
    [hμ₄ : IsProbabilityMeasure μ₄]:
    ∃ (A : Type (max u_1 u_2 u_3 u_4)) (_ : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' X₄' : A → α),
    IsProbabilityMeasure μA ∧
    iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃', X₄'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧ Measurable X₄'
      ∧ IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃
      ∧ IdentDistrib X₄' X₄ μA μ₄ ∧ FiniteRange X₁' ∧ FiniteRange X₂'
      ∧ FiniteRange X₃' ∧ FiniteRange X₄' := by
    have : Nonempty α := μ₁.nonempty_of_neZero.map X₁
    obtain ⟨A, mA, μA, X₁', X₂', X₃', X₄', hμA, hind, hX₁, hX₂, hX₃, hX₄, hId₁, hId₂, hId₃, hId₄⟩ :=
      independent_copies4_nondep hX₁ hX₂ hX₃ hX₄ μ₁ μ₂ μ₃ μ₄
    rcases identDistrib_of_finiteRange hX₁ hId₁.symm with ⟨X₁'', hX₁'', hX₁''_finite, hX₁''_eq⟩
    rcases identDistrib_of_finiteRange hX₂ hId₂.symm with ⟨X₂'', hX₂'', hX₂''_finite, hX₂''_eq⟩
    rcases identDistrib_of_finiteRange hX₃ hId₃.symm with ⟨X₃'', hX₃'', hX₃''_finite, hX₃''_eq⟩
    rcases identDistrib_of_finiteRange hX₄ hId₄.symm with ⟨X₄'', hX₄'', hX₄''_finite, hX₄''_eq⟩
    use A, mA, μA, X₁'', X₂'', X₃'', X₄''
    refine ⟨hμA, ?_, hX₁'', hX₂'', hX₃'', hX₄'', ?_, ?_, ?_, ?_, hX₁''_finite, hX₂''_finite,
        hX₃''_finite, hX₄''_finite⟩
    · apply hind.ae_eq
      intro i; fin_cases i
      all_goals simp [hX₁''_eq.symm, hX₂''_eq.symm, hX₃''_eq.symm, hX₄''_eq.symm]
    · convert IdentDistrib.trans _ hId₁
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₁'') hX₁''_eq
    · convert IdentDistrib.trans _ hId₂
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₂'') hX₂''_eq
    · convert IdentDistrib.trans _ hId₃
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₃'') hX₃''_eq
    · convert IdentDistrib.trans _ hId₄
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₄'') hX₄''_eq

end IdentDistrib
end ProbabilityTheory
