import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import PFR.Mathlib.MeasureTheory.Constructions.Pi
import PFR.Mathlib.Probability.Independence.Basic
import PFR.ForMathlib.FiniteRange

-- TODO: Change `ae_snd` to assume `Measurable p`

noncomputable section

open MeasureTheory Measure Filter Set
open scoped Topology BigOperators MeasureTheory ENNReal NNReal

attribute [symm] ProbabilityTheory.IdentDistrib.symm

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}

attribute [mk_iff] IdentDistrib

lemma identDistrib_id_left {X : α → β} (hX : AEMeasurable X μ) : IdentDistrib id X (μ.map X) μ where
  aemeasurable_fst := aemeasurable_id
  aemeasurable_snd := hX
  map_eq := by simp

lemma identDistrib_id_right {X : α → β} (hX : AEMeasurable X μ) : IdentDistrib X id μ (μ.map X) :=
  (identDistrib_id_left hX).symm

@[simp] lemma identDistrib_id {μ ν : Measure α} : IdentDistrib id id μ ν ↔ μ = ν := by
  simp [identDistrib_iff id id μ ν, aemeasurable_id]

/-- The first projection in a product space with measure `μ.prod ν` is distributed like `μ`. -/
lemma IdentDistrib.fst_id
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure ν] :
    IdentDistrib Prod.fst id (μ.prod ν) μ := by
  have : μ = (μ.prod ν).map Prod.fst := by simp
  nth_rewrite 2 [this]
  exact identDistrib_id_right measurable_fst.aemeasurable

/-- The second projection in a product space with measure `μ.prod ν` is distributed like `ν`. -/
lemma IdentDistrib.snd_id
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IdentDistrib Prod.snd id (μ.prod ν) ν := by
  have : ν = (μ.prod ν).map Prod.snd := by simp
  nth_rewrite 2 [this]
  exact identDistrib_id_right measurable_snd.aemeasurable

protected lemma IdentDistrib.cond (hs : MeasurableSet s) (hf' : Measurable f') (hg' : Measurable g')
    (hfg : IdentDistrib (fun a ↦ (f a, f' a)) (fun b ↦ (g b, g' b)) μ ν) :
    IdentDistrib f g (μ[|f' ⁻¹' s]) (ν[|g' ⁻¹' s]) where
  aemeasurable_fst := (measurable_fst.aemeasurable.comp_aemeasurable hfg.aemeasurable_fst).mono_ac
    cond_absolutelyContinuous
  aemeasurable_snd := (measurable_fst.aemeasurable.comp_aemeasurable hfg.aemeasurable_snd).mono_ac
    cond_absolutelyContinuous
  map_eq := by
    ext t ht
    rw [map_apply₀ _ ht.nullMeasurableSet, map_apply₀ _ ht.nullMeasurableSet,
      cond_apply _ (hg' hs), cond_apply _ (hf' hs)]
    congr
    · simpa only [map_apply₀ (hfg.comp measurable_snd).aemeasurable_fst hs.nullMeasurableSet,
        map_apply₀ (hfg.comp measurable_snd).aemeasurable_snd hs.nullMeasurableSet]
        using congr_fun (congr_arg (⇑) (hfg.comp measurable_snd).map_eq) s
    · rw [inter_comm, inter_comm (g' ⁻¹' _)]
      simpa only [map_apply₀ hfg.aemeasurable_fst (ht.prod hs).nullMeasurableSet,
        map_apply₀ hfg.aemeasurable_snd (ht.prod hs).nullMeasurableSet]
        using congr_fun (congr_arg (⇑) hfg.map_eq) (t ×ˢ s)
    · exact (hfg.comp measurable_fst).aemeasurable_snd.mono_ac cond_absolutelyContinuous
    · exact (hfg.comp measurable_fst).aemeasurable_fst.mono_ac cond_absolutelyContinuous

/-- A function is identically distributed to itself composed with a measurable embedding of conull
range. -/
lemma identDistrib_comp_left {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) : IdentDistrib (f ∘ i) f (μ.comap i) μ where
  aemeasurable_fst := (hf.comp hi.measurable).aemeasurable
  aemeasurable_snd := hf.aemeasurable
  map_eq := by rw [← Measure.map_map hf hi.measurable, hi.map_comap, restrict_eq_self_of_ae_mem hi']

/-- A function is identically distributed to itself composed with a measurable embedding of conull
range. -/
lemma identDistrib_comp_right {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) : IdentDistrib f (f ∘ i) μ (μ.comap i) :=
  (identDistrib_comp_left hi hi' hf).symm

-- TODO: Can we get rid of the measurability assumption in the following two?
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/docs.23MeasureTheory.2EMeasure.2Emap_map
/-- Composing identically distributed functions with a measurable embedding of conull range
gives identically distributed functions. -/
lemma IdentDistrib.comp_left {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) (hfg : IdentDistrib f g μ ν) : IdentDistrib (f ∘ i) g (μ.comap i) ν :=
  (identDistrib_comp_left hi hi' hf).trans hfg

/-- Composing identically distributed functions with a measurable embedding of conull range
gives identically distributed functions. -/
lemma IdentDistrib.comp_right {i : δ → β} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂ν, a ∈ range i)
    (hg : Measurable g) (hfg : IdentDistrib f g μ ν) : IdentDistrib f (g ∘ i) μ (ν.comap i) :=
  hfg.trans $ identDistrib_comp_right hi hi' hg

end ProbabilityTheory

open MeasureTheory ProbabilityTheory Function Set BigOperators

namespace ProbabilityTheory
section IdentDistrib
variable {Ω Ω' α ι β β' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω → β} {f' g' : Ω' → β}

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem IdentDistrib.prod_mk (hff' : IdentDistrib f f' μ ν) (hgg' : IdentDistrib g g' μ ν)
    (h : IndepFun f g μ) (h' : IndepFun f' g' ν) :
    IdentDistrib (fun x ↦ (f x, g x)) (fun x ↦ (f' x, g' x)) μ ν where
  aemeasurable_fst := hff'.aemeasurable_fst.prod_mk hgg'.aemeasurable_fst
  aemeasurable_snd := hff'.aemeasurable_snd.prod_mk hgg'.aemeasurable_snd
  map_eq := by
    rw [indepFun_iff_map_prod_eq_prod_map_map' hff'.aemeasurable_fst hgg'.aemeasurable_fst] at h
    rw [indepFun_iff_map_prod_eq_prod_map_map' hff'.aemeasurable_snd hgg'.aemeasurable_snd] at h'
    rw [h, h', hff'.map_eq, hgg'.map_eq]

variable [Mul β] [MeasurableMul₂ β] [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
@[to_additive]
theorem IdentDistrib.mul
    (hff' : IdentDistrib f f' μ ν) (hgg' : IdentDistrib g g' μ ν)
    (h : IndepFun f g μ) (h' : IndepFun f' g' ν) :
    IdentDistrib (f * g) (f' * g') μ ν :=
  hff'.prod_mk hgg' h h' |>.comp_of_aemeasurable measurable_mul.aemeasurable

variable [MeasurableSpace α] [MeasurableSpace β]

/-- A random variable is identically distributed to its pullbacks. -/
lemma identDistrib_map {X : Ω → α} (hX : Measurable X) {f : α → β} (hf : Measurable f)
    (μ : Measure Ω) : IdentDistrib f (f ∘ X) (μ.map X) μ where
  aemeasurable_fst := hf.aemeasurable
  aemeasurable_snd := (hf.comp hX).aemeasurable
  map_eq := map_map hf hX

lemma identDistrib_ulift_self {X : Ω → α} (hX : Measurable X) :
    IdentDistrib X (X ∘ ULift.down) μ (μ.comap ULift.down) := by
  have hX' : Measurable (X ∘ ULift.down : ULift Ω → α) := hX.comp measurable_down
  refine' ⟨hX.aemeasurable, hX'.aemeasurable, _⟩
  ext s hs
  rw [Measure.map_apply (μ := (μ.comap ULift.down)) hX' hs,
    Measure.comap_apply _ ULift.down_injective _ _ (hX' hs), Set.preimage_comp,
    Set.image_preimage_eq _ ULift.down_surjective, Measure.map_apply hX hs]
  intro s hs
  change MeasurableSet (ULift.down ⁻¹' (ULift.down '' s))
  rwa [Set.preimage_image_eq _ ULift.down_injective]

/-- To show identical distribution of two random variables on a mixture of probability measures, it suffices to do so on each non-trivial component. -/
-- in fact this is an if and only if
lemma identDistrib_of_sum {X : Ω → α} {Y : Ω' → α} [Fintype T] {μ : T → Measure Ω}
    {μ' : T → Measure Ω'} {w : T → ENNReal} (hX : Measurable X) (hY : Measurable Y)
    (h_ident : ∀ y, w y ≠ 0 → IdentDistrib X Y (μ y) (μ' y)) :
    IdentDistrib X Y (∑ y : T, (w y) • (μ y)) (∑ y : T, (w y) • (μ' y)) where
  aemeasurable_fst := hX.aemeasurable
  aemeasurable_snd := hY.aemeasurable
  map_eq := by
    rw [← Measure.mapₗ_apply_of_measurable hX, ← Measure.mapₗ_apply_of_measurable hY]
    simp
    congr with y E _
    rcases eq_or_ne (w y) 0 with hy | hy
    . simp [hy]
    congr 3
    rw [Measure.mapₗ_apply_of_measurable hX, Measure.mapₗ_apply_of_measurable hY]
    exact (h_ident y hy).map_eq

/-- A random variable is identically distributed to its lift to a product space (in the first factor). -/
lemma identDistrib_comp_fst {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ'] : IdentDistrib (X ∘ Prod.fst) X (μ.prod μ') μ where
  aemeasurable_fst := (hX.comp measurable_fst).aemeasurable
  aemeasurable_snd := hX.aemeasurable
  map_eq := by
    rw [← Measure.map_map hX measurable_fst, Measure.map_fst_prod]
    congr
    simp

/-- A random variable is identically distributed to its lift to a product space (in the second factor). -/
lemma identDistrib_comp_snd {X : Ω → α} (hX : Measurable X) (μ : Measure Ω) (μ' : Measure Ω')
  [SigmaFinite μ] [IsProbabilityMeasure μ'] : IdentDistrib (X ∘ Prod.snd) X (μ'.prod μ) μ where
  aemeasurable_fst := (hX.comp measurable_snd).aemeasurable
  aemeasurable_snd := hX.aemeasurable
  map_eq := by
    rw [← Measure.map_map hX measurable_snd, Measure.map_snd_prod]
    congr
    simp

/-- For `X, Y` random variables, one can find independent copies `X', Y'` of `X, Y`. -/
lemma independent_copies {X : Ω → α} {Y : Ω' → β} (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    ∃ ν : Measure (α × β), ∃ X' : α × β → α, ∃ Y' : α × β → β, IsProbabilityMeasure ν
      ∧ Measurable X' ∧ Measurable Y' ∧ IndepFun X' Y' ν
      ∧ IdentDistrib X' X ν μ ∧ IdentDistrib Y' Y ν μ' := by
  have := MeasureTheory.isProbabilityMeasure_map hX.aemeasurable (μ := μ)
  have := MeasureTheory.isProbabilityMeasure_map hY.aemeasurable (μ := μ')
  exact ⟨(μ.map X).prod (μ'.map Y), _, _, inferInstance, measurable_fst, measurable_snd,
    indepFun_fst_snd, ⟨measurable_fst.aemeasurable, hX.aemeasurable, by simp⟩,
    measurable_snd.aemeasurable, hY.aemeasurable, by simp⟩

/-- For `X, Y` random variables, one can find independent copies `X', Y'` of `X, Y`. Version
formulated in spaces with a canonical measures. -/
lemma independent_copies_two {Ω : Type u} {Ω' : Type v} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (ℙ : Measure Ω)] [IsProbabilityMeasure (ℙ : Measure Ω')]
    {X : Ω → α} {Y : Ω' → β} (hX : Measurable X) (hY : Measurable Y) :
    ∃ (Ω'' : Type (max u v)) (m'' : MeasureSpace Ω'') (X' : Ω'' → α) (Y' : Ω'' → β),
    IsProbabilityMeasure (ℙ : Measure Ω'') ∧ Measurable X' ∧ Measurable Y' ∧
      IndepFun X' Y' ∧ IdentDistrib X' X ∧ IdentDistrib Y' Y := by
  refine ⟨Ω × Ω', by infer_instance, X ∘ Prod.fst, Y ∘ Prod.snd, by infer_instance,
    hX.comp measurable_fst, hY.comp measurable_snd, ?_, ?_, ?_⟩
  · exact indepFun_fst_snd.comp hX hY
  · refine ⟨(hX.comp measurable_fst).aemeasurable, hX.aemeasurable, ?_⟩
    have : (ℙ : Measure (Ω × Ω')) = (ℙ : Measure Ω).prod (ℙ : Measure Ω') := rfl
    simp [← Measure.map_map hX measurable_fst, this]
  · refine ⟨(hY.comp measurable_snd).aemeasurable, hY.aemeasurable, ?_⟩
    have : (ℙ : Measure (Ω × Ω')) = (ℙ : Measure Ω).prod (ℙ : Measure Ω') := rfl
    simp [← Measure.map_map hY measurable_snd, this]

/-- Let `Xᵢ : Ωᵢ → Sᵢ` be random variables for `i = 1,...,k`.
Then there exist jointly independent random variables `Xᵢ' : Ω' → Sᵢ` for `i=1,...,k`
such that each `Xᵢ'` is a copy of `Xᵢ`. -/
lemma independent_copies' {I : Type u} [Fintype I] {α : I → Type u'}
    [mS : ∀ i : I, MeasurableSpace (α i)] {Ω : I → Type v}
    [mΩ : ∀ i : I, MeasurableSpace (Ω i)] (X : ∀ i : I, Ω i → α i) (hX : ∀ i : I, Measurable (X i))
    (μ : ∀ i : I, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ∃ (A : Type (max u v)) (mA : MeasurableSpace A) (μA : Measure A) (X' : ∀ i, A → α i),
    IsProbabilityMeasure μA ∧
    iIndepFun mS X' μA ∧
    ∀ i : I, Measurable (X' i) ∧ IdentDistrib (X' i) (X i) μA (μ i) := by
  refine ⟨Π i, Ω i, inferInstance, .pi μ, fun i ↦ X i ∘ eval i, inferInstance, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [iIndepFun_iff]
    intro t s hs
    choose! u _ hus using hs
    simp (config := {contextual := true}) [← hus, preimage_comp]
    simp_rw [← Finset.mem_coe, ← Set.pi_def, pi_pi_finset]
  · exact (hX i).comp (measurable_pi_apply i)
  · refine ⟨(hX i).comp (measurable_pi_apply i) |>.aemeasurable, (hX i).aemeasurable, ?_⟩
    rw [← Measure.map_map (hX i) (measurable_pi_apply i), Measure.map_eval_pi]

/-- A version with exactly 3 random variables that have the same codomain.
It's unfortunately incredibly painful to prove this from the general case. -/
lemma independent_copies3_nondep {α : Type u}
    [mS : MeasurableSpace α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃)
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂] [hμ₃ : IsProbabilityMeasure μ₃] :
    ∃ (A : Type (max u_1 u_2 u_3)) (mA : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' : A → α),
    IsProbabilityMeasure μA ∧
    iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧
      IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃ := by
  let Ω₁' : Type (max u_1 u_2 u_3) := ULift.{max u_2 u_3} Ω₁
  let Ω₂' : Type (max u_1 u_2 u_3) := ULift.{max u_1 u_3} Ω₂
  let Ω₃' : Type (max u_1 u_2 u_3) := ULift.{max u_1 u_2} Ω₃
  let Ω : Fin 3 → Type (max u_1 u_2 u_3) := ![Ω₁', Ω₂', Ω₃']
  let mΩ : (i : Fin 3) → MeasurableSpace (Ω i) :=
    Fin.cases (inferInstance : MeasurableSpace Ω₁') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₂') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₃') Fin.rec0
  let X : (i : Fin 3) → Ω i → α :=
    Fin.cases (X₁ ∘ ULift.down) <| Fin.cases (X₂ ∘ ULift.down) <| Fin.cases (X₃ ∘ ULift.down) Fin.rec0
  have hX : ∀ (i : Fin 3), @Measurable _ _ (mΩ i) mS (X i) :=
    Fin.cases (hX₁.comp measurable_down) <|
    Fin.cases (hX₂.comp measurable_down) <|
    Fin.cases (hX₃.comp measurable_down) Fin.rec0
  let μ : (i : Fin 3) → @Measure (Ω i) (mΩ i) :=
    Fin.cases (μ₁.comap ULift.down) <|
    Fin.cases (μ₂.comap ULift.down) <|
    Fin.cases (μ₃.comap ULift.down) Fin.rec0
  have hμ : (i : Fin 3) → IsProbabilityMeasure (μ i) :=
    Fin.cases isProbabilityMeasure_comap_down <|
    Fin.cases isProbabilityMeasure_comap_down <|
    Fin.cases isProbabilityMeasure_comap_down Fin.rec0
  obtain ⟨A, mA, μA, X', hμ, hi, hX'⟩ := independent_copies' X hX μ
  refine ⟨A, mA, μA, X' 0, X' 1, X' 2, hμ, ?_,
    (hX' 0).1, (hX' 1).1, (hX' 2).1,
    (hX' 0).2.trans ((identDistrib_ulift_self hX₁).symm),
    (hX' 1).2.trans (identDistrib_ulift_self hX₂).symm,
    (hX' 2).2.trans (identDistrib_ulift_self hX₃).symm⟩
  convert hi; ext i; fin_cases i <;> rfl

/-- A version with exactly 4 random variables that have the same codomain.
It's unfortunately incredibly painful to prove this from the general case. -/
lemma independent_copies4_nondep {α : Type u}
    [mS : MeasurableSpace α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3} {Ω₄ : Type u_4}
    [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    [mΩ₃ : MeasurableSpace Ω₃] [mΩ₄ : MeasurableSpace Ω₄]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α} {X₄ : Ω₄ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃) (hX₄ : Measurable X₄)
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃) (μ₄ : Measure Ω₄)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂]
    [hμ₃ : IsProbabilityMeasure μ₃] [hμ₄ : IsProbabilityMeasure μ₄] :
    ∃ (A : Type (max u_1 u_2 u_3 u_4)) (mA : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' X₄' : A → α),
    IsProbabilityMeasure μA ∧
    iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃', X₄'] μA ∧
    Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧ Measurable X₄' ∧
    IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧
    IdentDistrib X₃' X₃ μA μ₃ ∧ IdentDistrib X₄' X₄ μA μ₄ := by
  let Ω₁' : Type (max u_1 u_2 u_3 u_4) := ULift.{max u_2 u_3 u_4} Ω₁
  let Ω₂' : Type (max u_1 u_2 u_3 u_4) := ULift.{max u_1 u_3 u_4} Ω₂
  let Ω₃' : Type (max u_1 u_2 u_3 u_4) := ULift.{max u_1 u_2 u_4} Ω₃
  let Ω₄' : Type (max u_1 u_2 u_3 u_4) := ULift.{max u_1 u_2 u_3} Ω₄
  let Ω : Fin 4 → Type (max u_1 u_2 u_3 u_4) := ![Ω₁', Ω₂', Ω₃', Ω₄']
  let mΩ : (i : Fin 4) → MeasurableSpace (Ω i) :=
    Fin.cases (inferInstance : MeasurableSpace Ω₁') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₂') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₃') <|
    Fin.cases (inferInstance : MeasurableSpace Ω₄') Fin.rec0
  let X : (i : Fin 4) → Ω i → α :=
    Fin.cases (X₁ ∘ ULift.down) <| Fin.cases (X₂ ∘ ULift.down) <|
    Fin.cases (X₃ ∘ ULift.down) <| Fin.cases (X₄ ∘ ULift.down) Fin.rec0
  have hX : ∀ (i : Fin 4), @Measurable _ _ (mΩ i) mS (X i) :=
    Fin.cases (hX₁.comp measurable_down) <| Fin.cases (hX₂.comp measurable_down) <|
    Fin.cases (hX₃.comp measurable_down) <| Fin.cases (hX₄.comp measurable_down) Fin.rec0
  let μ : (i : Fin 4) → @Measure (Ω i) (mΩ i) :=
    Fin.cases (μ₁.comap ULift.down) <| Fin.cases (μ₂.comap ULift.down) <|
    Fin.cases (μ₃.comap ULift.down) <| Fin.cases (μ₄.comap ULift.down) Fin.rec0
  let hμ : (i : Fin 4) → IsProbabilityMeasure (μ i) :=
    Fin.cases isProbabilityMeasure_comap_down <| Fin.cases isProbabilityMeasure_comap_down <|
    Fin.cases isProbabilityMeasure_comap_down <| Fin.cases isProbabilityMeasure_comap_down Fin.rec0
  obtain ⟨A, mA, μA, X', hμ, hi, hX'⟩ := independent_copies' X hX μ
  refine ⟨A, mA, μA, X' 0, X' 1, X' 2, X' 3, hμ, ?_,
    (hX' 0).1, (hX' 1).1, (hX' 2).1, (hX' 3).1,
    (hX' 0).2.trans ((identDistrib_ulift_self hX₁).symm),
    (hX' 1).2.trans ((identDistrib_ulift_self hX₂).symm),
    (hX' 2).2.trans ((identDistrib_ulift_self hX₃).symm),
    (hX' 3).2.trans ((identDistrib_ulift_self hX₄).symm)⟩
  convert hi; ext i; fin_cases i <;> rfl

/-- If `X` has identical distribution to `X₀`, and `X₀` has finite range, then `X` is almost everywhere equivalent to a random variable of finite range. -/
lemma identDistrib_of_finiteRange {Ω Ω₀ S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace S] [MeasurableSingletonClass S] [hS: Nonempty S] {μ: Measure Ω} {μ₀: Measure Ω₀} {X₀: Ω₀ → S} [FiniteRange X₀] {X : Ω → S} (hX: Measurable X) (hi : IdentDistrib X₀ X μ₀ μ) : ∃ X' : Ω → S, Measurable X' ∧ FiniteRange X' ∧ X' =ᵐ[μ] X := by
  set A := FiniteRange.toFinset X₀
  classical
  let X' (ω : Ω) : S := if (X ω ∈ A) then X ω else hS.some
  use X'
  constructor
  . exact Measurable.ite (MeasurableSet.preimage (Finset.measurableSet A) hX) hX measurable_const
  constructor
  . apply finiteRange_of_finset X' (A ∪ {hS.some})
    intro ω
    simp
    by_cases h: X ω ∈ A
    . left; simp at h; simp [X', h]
    · right
      simp only [ite_eq_right_iff, X']
      exact fun h' ↦ absurd h' h
  apply Filter.eventuallyEq_of_mem (s := X ⁻¹' A)
  . simp [ae]
    rw [← Set.preimage_compl, ← IdentDistrib.measure_preimage_eq hi]
    . convert measure_empty
      ext ω
      simp [A]
    measurability
  intro ω
  simp only [mem_preimage, Finset.mem_coe, ite_eq_left_iff, X']
  tauto

/-- A version of `independent_copies` that guarantees that the copies have `FiniteRange` if the original variables do. -/
lemma independent_copies_finiteRange {X : Ω → α} {Y : Ω' → β} (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]   [MeasurableSingletonClass α] [Nonempty α] [MeasurableSingletonClass β] [Nonempty β]
    (μ : Measure Ω) (μ' : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] :
    ∃ ν : Measure (α × β), ∃ X' : α × β → α, ∃
    Y' : α × β → β, IsProbabilityMeasure ν
      ∧ Measurable X' ∧ Measurable Y' ∧ IndepFun X' Y' ν
      ∧ IdentDistrib X' X ν μ ∧ IdentDistrib Y' Y ν μ' ∧ FiniteRange X' ∧ FiniteRange Y'  := by
  obtain ⟨ν, X', Y', hν, hX', hY', hind, hIdX, hIdY⟩ := independent_copies hX hY μ μ'
  rcases identDistrib_of_finiteRange hX' hIdX.symm with ⟨X'', hX'', hX''_finite, hX''_eq⟩
  rcases identDistrib_of_finiteRange hY' hIdY.symm with ⟨Y'', hY'', hY''_finite, hY''_eq⟩
  use ν, X'', Y''
  refine ⟨hν, hX'', hY'', ?_, ?_, ?_, hX''_finite, hY''_finite⟩
  . exact IndepFun.ae_eq' hind hX''_eq.symm hY''_eq.symm
  . convert IdentDistrib.trans _ hIdX
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX'') hX''_eq
  . convert IdentDistrib.trans _ hIdY
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hY'') hY''_eq

/-- A version of `independent_copies3_nondep` that guarantees that the copies have `FiniteRange` if the original variables do. -/
lemma independent_copies3_nondep_finiteRange {α : Type u}
    [mS : MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃)
    [FiniteRange X₁] [FiniteRange X₂] [FiniteRange X₃]
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂] [hμ₃ : IsProbabilityMeasure μ₃] :
    ∃ (A : Type (max u_1 u_2 u_3)) (mA : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' : A → α),
    IsProbabilityMeasure μA ∧
    iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧
      IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃ ∧ FiniteRange X₁' ∧ FiniteRange X₂' ∧ FiniteRange X₃' := by
    obtain ⟨A, mA, μA, X₁', X₂', X₃', hμA, hind, hX₁, hX₂, hX₃, hId₁, hId₂, hId₃⟩ := independent_copies3_nondep hX₁ hX₂ hX₃ μ₁ μ₂ μ₃
    rcases identDistrib_of_finiteRange hX₁ hId₁.symm with ⟨X₁'', hX₁'', hX₁''_finite, hX₁''_eq⟩
    rcases identDistrib_of_finiteRange hX₂ hId₂.symm with ⟨X₂'', hX₂'', hX₂''_finite, hX₂''_eq⟩
    rcases identDistrib_of_finiteRange hX₃ hId₃.symm with ⟨X₃'', hX₃'', hX₃''_finite, hX₃''_eq⟩
    use A, mA, μA, X₁'', X₂'', X₃''
    refine ⟨hμA, ?_, hX₁'', hX₂'', hX₃'', ?_, ?_, ?_, hX₁''_finite, hX₂''_finite, hX₃''_finite⟩
    . apply iIndepFun.ae_eq hind
      intro i; fin_cases i
      all_goals simp [hX₁''_eq.symm, hX₂''_eq.symm, hX₃''_eq.symm]
    . convert IdentDistrib.trans _ hId₁
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₁'') hX₁''_eq
    . convert IdentDistrib.trans _ hId₂
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₂'') hX₂''_eq
    convert IdentDistrib.trans _ hId₃
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₃'') hX₃''_eq

/-- A version of `independent_copies4_nondep` that guarantees that the copies have `FiniteRange` if the original variables do. -/
lemma independent_copies4_nondep_finiteRange {α : Type u}
    [mS : MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
    {Ω₁ : Type u_1} {Ω₂ : Type u_2} {Ω₃ : Type u_3} {Ω₄ : Type u_4}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] [MeasurableSpace Ω₄]
    {X₁ : Ω₁ → α} {X₂ : Ω₂ → α} {X₃ : Ω₃ → α} {X₄ : Ω₄ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃) (hX₄ : Measurable X₄)
    [FiniteRange X₁] [FiniteRange X₂] [FiniteRange X₃] [FiniteRange X₄]
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃) (μ₄ : Measure Ω₄)
    [hμ₁ : IsProbabilityMeasure μ₁] [hμ₂ : IsProbabilityMeasure μ₂] [hμ₃ : IsProbabilityMeasure μ₃] [hμ₄ : IsProbabilityMeasure μ₄]:
    ∃ (A : Type (max u_1 u_2 u_3 u_4)) (mA : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' X₄' : A → α),
    IsProbabilityMeasure μA ∧
    iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃', X₄'] μA ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧ Measurable X₄' ∧ IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃ ∧ IdentDistrib X₄' X₄ μA μ₄ ∧ FiniteRange X₁' ∧ FiniteRange X₂' ∧ FiniteRange X₃' ∧ FiniteRange X₄' := by
    obtain ⟨A, mA, μA, X₁', X₂', X₃', X₄', hμA, hind, hX₁, hX₂, hX₃, hX₄, hId₁, hId₂, hId₃, hId₄⟩ := independent_copies4_nondep hX₁ hX₂ hX₃ hX₄ μ₁ μ₂ μ₃ μ₄
    rcases identDistrib_of_finiteRange hX₁ hId₁.symm with ⟨X₁'', hX₁'', hX₁''_finite, hX₁''_eq⟩
    rcases identDistrib_of_finiteRange hX₂ hId₂.symm with ⟨X₂'', hX₂'', hX₂''_finite, hX₂''_eq⟩
    rcases identDistrib_of_finiteRange hX₃ hId₃.symm with ⟨X₃'', hX₃'', hX₃''_finite, hX₃''_eq⟩
    rcases identDistrib_of_finiteRange hX₄ hId₄.symm with ⟨X₄'', hX₄'', hX₄''_finite, hX₄''_eq⟩
    use A, mA, μA, X₁'', X₂'', X₃'', X₄''
    refine ⟨hμA, ?_, hX₁'', hX₂'', hX₃'', hX₄'', ?_, ?_, ?_, ?_, hX₁''_finite, hX₂''_finite, hX₃''_finite, hX₄''_finite⟩
    . apply iIndepFun.ae_eq hind
      intro i; fin_cases i
      all_goals simp [hX₁''_eq.symm, hX₂''_eq.symm, hX₃''_eq.symm, hX₄''_eq.symm]
    . convert IdentDistrib.trans _ hId₁
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₁'') hX₁''_eq
    . convert IdentDistrib.trans _ hId₂
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₂'') hX₂''_eq
    . convert IdentDistrib.trans _ hId₃
      exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₃'') hX₃''_eq
    convert IdentDistrib.trans _ hId₄
    exact IdentDistrib.of_ae_eq (Measurable.aemeasurable hX₄'') hX₄''_eq

end IdentDistrib
end ProbabilityTheory
