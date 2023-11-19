import PFR.Entropy.KernelMutualInformation

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

section ProdMkRight

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Define a `kernel (α × γ) β` from a `kernel α β` by taking the comap of the projection. -/
def prodMkRight (κ : kernel α β) (γ : Type*) [MeasurableSpace γ] : kernel (α × γ) β :=
  comap κ Prod.fst measurable_fst

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : β → γ} {g : γ → α}

theorem prodMkRight_apply (κ : kernel α β) (ca : α × γ) : prodMkRight κ γ ca = κ ca.fst := rfl

theorem prodMkRight_apply' (κ : kernel α β) (ca : α × γ) (s : Set β) :
    prodMkRight κ γ ca s = κ ca.fst s := rfl

theorem lintegral_prodMkRight (κ : kernel α β) (ca : α × γ) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkRight κ γ ca = ∫⁻ b, g b ∂κ ca.fst := rfl

instance IsMarkovKernel.prodMkRight (κ : kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkRight κ γ) := by rw [kernel.prodMkRight]; infer_instance

instance IsFiniteKernel.prodMkRight (κ : kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkRight κ γ) := by rw [kernel.prodMkRight]; infer_instance

instance IsSFiniteKernel.prodMkRight (κ : kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkRight κ γ) := by rw [kernel.prodMkRight]; infer_instance

/- Todo: could `Measure.prod_apply` be generalized to s-finite measures?
It would allow replacing `IsFiniteKernel η` by `IsSFiniteKernel η`
Todo: this should be named `prod_apply` and the existing lemma with that name should be
`prod_apply'` -/
lemma prod_apply'' (κ : kernel α β) [IsSFiniteKernel κ] (η : kernel α γ) [IsFiniteKernel η]
    (a : α) :
    (κ ×ₖ η) a = (κ a).prod (η a) := by
  ext s hs
  rw [prod_apply _ _ _ hs, Measure.prod_apply hs]
  rfl

end ProdMkRight

variable {T T' G : Type*}
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  [Fintype T'] [Nonempty T'] [MeasurableSpace T'] [MeasurableSingletonClass T']
  [Fintype G] [Nonempty G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G] [MeasurableSub₂ G] [MeasurableAdd₂ G]
  {κ : kernel T G} {η : kernel T' G} {μ : Measure T}  {ν : Measure T'}

noncomputable
def rdistm (μ : Measure G) (ν : Measure G) : ℝ :=
    Hm[(μ.prod ν).map (fun x ↦ x.1 - x.2)] - Hm[μ]/2 - Hm[ν]/2

/-- The Ruzsa distance `dist X Y` between two random variables is defined as
$H[X'-Y'] - H[X']/2 - H[Y']/2$, where $X',Y'$ are independent copies of $X, Y$. -/
noncomputable
def rdist (κ : kernel T G) (η : kernel T' G) (μ : Measure T) (ν : Measure T') : ℝ :=
  (μ.prod ν)[fun p ↦ rdistm (κ p.1) (η p.2)]

/-- Needed a new separator here, chose `#` arbitrarily, but am open to other suggestions -/
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

end ProbabilityTheory.kernel
