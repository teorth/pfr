open BigOperators

noncomputable def Measure.mul (c : NNReal) {Ω : Type*} [MeasureSpace Ω] (μ : Measure Ω) : Measure Ω where
  measureOf := (fun E ↦ c * μ E)
  empty := by simp
  mono := by intros; dsimp; gcongr
  iUnion_nat := by
    intro E
    dsimp
    rw [ENNReal.tsum_mul_left]
    gcongr
    exact OuterMeasure.iUnion_nat ↑μ fun i => E i
  m_iUnion := by
    intro E hE hDisjoint
    dsimp
    rw [ENNReal.tsum_mul_left]
    congr
    exact Measure.m_iUnion μ hE hDisjoint
  trimmed := by
    rw [MeasureTheory.OuterMeasure.trim_eq_iInf']


