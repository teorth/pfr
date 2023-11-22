import PFR.entropy_basic
import PFR.ruzsa_distance

/-!
# The 100% version of entropic PFR

Here we show entropic PFR in the case of doubling constant zero.
-/

open MeasureTheory ProbabilityTheory Real

variable {Ω Ω' G : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} (hμ : IsProbabilityMeasure μ) [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'} (hμ' : IsProbabilityMeasure μ') [AddCommGroup G] [Fintype G] {X : Ω → G} (hX : Measurable X) {X' : Ω' → G} (hX' : Measurable X')

/-- The symmetry group Sym of X: the set of all $h ∈ G$ such that $X+h$ as an identical distribution to $X$. -/
def symm_group (X : Ω → G) : Set G := sorry

/-- The symmetry group is a group. -/
lemma symm_group_is_subgroup : ∃ H : AddSubgroup G, H.carrier = symm_group X := sorry

/-- $$ d[X; U_{\mathrm{Sym}[X]}] = \tfrac{1}{2} H[X] - \tfrac{1}{2} \log |\mathrm{Sym}[X]|.$$ -/
lemma dist_to_symm_group (U : G → G) (ν : Measure G) (hν: IsProbabilityMeasure ν) (hU: isUniform (symm_group X) U ν) : d[X; μ # U; ν ] = H[X; μ]/2 - H[U;ν]/2 := sorry

/-- If $d[X;X]=0$, and $x,y \in G$ are such that $P[X=x], P[X=y]>0$, then $x-y \in \mathrm{Sym}[X]$.
-/
lemma diff_in_symm_group (hdist : d[X; μ # X; μ ] = 0) (x y : G)  (hx: μ (X⁻¹' {x}) = 0)
(hy: μ (X⁻¹' {y}) = 0): x - y ∈ symm_group X := sorry

/-- If $d[X;X]=0$, then $\log |\mathrm{Sym}[X]| \geq H[X]$. -/
lemma ent_le_log_card_symm_group (hdist : d[X; μ # X; μ ] = 0) : 0 = 1 := sorry

/-- If $d[X;X]=0$, then there exists a subgroup $H \leq G$ such that $d[X;U_H] = 0$. -/
theorem dist_self_eq_zero_iff (hdist : d[X; μ # X; μ ] = 0): ∃ H : AddSubgroup G, ∃ U : G → G, ∃ ν : Measure G, IsProbabilityMeasure ν ∧ isUniform H.carrier U ν ∧ d[X; μ # U ; ν ] = 0 := by sorry

/-- If $d[X_1;X_2]=0$, then there exists a subgroup $H \leq G$ such that $d[X_1;U_H] = d[X_2;U_H] = 0$. Follows from the preceding claim by the triangle inequality. -/
theorem dist_eq_zero_iff (hdist : d[X; μ # X'; μ' ] = 0) : ∃ H : AddSubgroup G, ∃ U : G → G, ∃ ν : Measure G, IsProbabilityMeasure ν ∧ isUniform H U ν ∧ d[X; μ # U ; ν ] = 0 ∧ d[X'; μ' # U ; ν ] = 0:= by sorry
