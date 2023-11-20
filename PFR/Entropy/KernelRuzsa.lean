import PFR.Entropy.Group

/-!
# Ruzsa distance between kernels

## Main definitions

*

## Notations

* `dk[κ ; μ # η ; ν] = `

-/


open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators


namespace ProbabilityTheory.kernel

variable {T T' G : Type*}
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype T'] [Nonempty T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
  [Fintype G] [Nonempty G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G] [MeasurableSub₂ G] [MeasurableAdd₂ G]
  {κ : kernel T G} {η : kernel T' G} {μ : Measure T}  {ν : Measure T'}

noncomputable
def rdistm (μ : Measure G) (ν : Measure G) : ℝ :=
    Hm[(μ.prod ν).map (fun x ↦ x.1 - x.2)] - Hm[μ]/2 - Hm[ν]/2

noncomputable
def rdist (κ : kernel T G) (η : kernel T' G) (μ : Measure T) (ν : Measure T') : ℝ :=
  (μ.prod ν)[fun p ↦ rdistm (κ p.1) (η p.2)]

notation3:max "dk[" κ " ; " μ " # " η " ; " μ' "]" => rdist κ η μ μ'

lemma rdist_eq (κ : kernel T G) (η : kernel T' G) (μ : Measure T) (ν : Measure T')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    dk[κ ; μ # η ; ν] = (μ.prod ν)[fun p ↦ Hm[((κ p.1).prod (η p.2)).map (fun x ↦ x.1 - x.2)]]
      - Hk[κ, μ]/2 - Hk[η, ν]/2 := by
  simp_rw [rdist, rdistm, integral_eq_sum, smul_sub, Finset.sum_sub_distrib, smul_eq_mul]
  congr
  · simp_rw [Fintype.sum_prod_type, ← Finset.sum_mul,
      ← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul,
      ← Finset.mul_sum, Finset.sum_toReal_measure_singleton, Finset.coe_univ, measure_univ,
      ENNReal.one_toReal, mul_one, mul_div, ← Finset.sum_div, entropy, integral_eq_sum, smul_eq_mul]
  · simp_rw [Fintype.sum_prod_type_right, ← Finset.sum_mul, ← Set.singleton_prod_singleton,
      Measure.prod_prod, ENNReal.toReal_mul, ← Finset.sum_mul, Finset.sum_toReal_measure_singleton,
      Finset.coe_univ, measure_univ, ENNReal.one_toReal, one_mul,
      mul_div, ← Finset.sum_div, entropy, integral_eq_sum, smul_eq_mul]

lemma rdist_eq' (κ : kernel T G) (η : kernel T' G) [IsFiniteKernel κ] [IsFiniteKernel η]
    (μ : Measure T) (ν : Measure T') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    dk[κ ; μ # η ; ν] =
      Hk[map ((prodMkRight κ T') ×ₖ (prodMkLeft T η)) (fun x ↦ x.1 - x.2) measurable_sub, μ.prod ν]
      - Hk[κ, μ]/2 - Hk[η, ν]/2 := by
  rw [rdist_eq]
  congr with p
  simp only
  rw [map_apply, prod_apply'', prodMkLeft_apply, prodMkRight_apply]

lemma rdist_symm (κ : kernel T G) (η : kernel T' G) [IsFiniteKernel κ] [IsFiniteKernel η]
    (μ : Measure T) (ν : Measure T') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    dk[κ ; μ # η ; ν] = dk[η ; ν # κ ; μ] := by
  rw [rdist_eq', rdist_eq', sub_sub, sub_sub, add_comm]
  congr 1
  rw [← entropy_comap_swap, comap_map_comm, entropy_sub_comm, Measure.comap_swap, Measure.prod_swap,
    comap_prod_swap, map_map]
  congr

end ProbabilityTheory.kernel
