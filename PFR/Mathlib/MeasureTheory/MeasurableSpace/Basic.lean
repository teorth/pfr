import Mathlib.MeasureTheory.MeasurableSpace.Basic

section MeasurableEquiv
variable {α β γ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} {_ : MeasurableSpace γ}

/-- Canonical bijection between `(α × β) × γ` and `α × β × γ`. -/
def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ where
  toEquiv := Equiv.prodAssoc _ _ _
  measurable_toFun := (measurable_fst.comp measurable_fst).prod_mk
    ((measurable_snd.comp measurable_fst).prod_mk measurable_snd)
  measurable_invFun := (measurable_fst.prod_mk (measurable_fst.comp measurable_snd)).prod_mk
    (measurable_snd.comp measurable_snd)

-- attribute [simps] Equiv.punitProd

/-- Measurable equivalence with the product with the one-point space `Unit`.-/
def prodMKLeft_unit_equiv (α : Type*) [MeasurableSpace α] : (Unit × α) ≃ᵐ α where
  toEquiv := Equiv.punitProd α
  measurable_toFun := measurable_snd
  measurable_invFun := measurable_prod_mk_left

end MeasurableEquiv
