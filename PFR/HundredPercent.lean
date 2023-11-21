import PFR.entropy_basic
import PFR.ruzsa_distance

/-!
# The 100% version of entropic PFR

Here we show entropic PFR in the case of doubling constant zero.
-/

open MeasureTheory ProbabilityTheory

variable {Ω Ω' G : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'} [AddCommGroup G] [Fintype G] {X : Ω → G} {X' : Ω' → G}

/-- If $d[X_1;X_1]=0$, then there exists a subgroup $H \leq G$ such that $d[X_1;U_H] = 0$. -/
theorem dist_self_eq_zero_iff (hX : Measurable X) (hdist : d[X; μ # X; μ ] = 0) (hμ : IsProbabilityMeasure μ): ∃ H : AddSubgroup G, ∃ U : G → G, ∃ ν : Measure G, IsProbabilityMeasure ν ∧ isUniform H.carrier U ν ∧ d[X; μ # U ; ν ] = 0 := by sorry

/-- If $d[X_1;X_2]=0$, then there exists a subgroup $H \leq G$ such that $d[X_1;U_H] = d[X_2;U_H] = 0$. Follows from the preceding claim by the triangle inequality. -/
theorem dist_eq_zero_iff (hX : Measurable X) (hX' : Measurable X') (hdist : d[X; μ # X'; μ' ] = 0) (hμ : IsProbabilityMeasure μ) (hμ' : IsProbabilityMeasure μ'): ∃ H : AddSubgroup G, ∃ U : G → G, ∃ ν : Measure G, IsProbabilityMeasure ν ∧ isUniform H U ν ∧ d[X; μ # U ; ν ] = 0 ∧ d[X'; μ' # U ; ν ] = 0:= by sorry
