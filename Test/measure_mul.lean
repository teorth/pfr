import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory
open scoped BigOperators

-- Using mathlib, this is just `c • μ`
noncomputable def Measure.mul (c : NNReal) {Ω : Type*} [MeasureSpace Ω] (μ : Measure Ω) :
    Measure Ω where
  measureOf := (fun E ↦ c * μ E)
  empty := by simp
  mono := by intros; dsimp; gcongr
  iUnion_nat := by
    intro E
    dsimp
    rw [ENNReal.tsum_mul_left]
    gcongr
    apply measure_iUnion_le
  m_iUnion := by
    intro E hE hDisjoint
    dsimp
    rw [ENNReal.tsum_mul_left]
    congr
    exact Measure.m_iUnion μ hE hDisjoint
  trimmed := by
    sorry
    -- rw [MeasureTheory.OuterMeasure.trim_eq_iInf']
