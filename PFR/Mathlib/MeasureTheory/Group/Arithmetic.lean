import Mathlib.MeasureTheory.Group.Arithmetic
import PFR.ForMathlib.Pair

attribute [fun_prop] Measurable.div' Measurable.sub' Measurable.add' Measurable.mul'

-- I am surprised that this one is needed, as `fun_prop` already knows that
-- `(ω ↦ (f ω, g ω))` is measurable, from `Measurable.prod_mk` .
-- Doesn't `fun_prop` see through abbrevs?
-- (not sure this one is worth upstreaming, better fix `fun_prop`)
@[fun_prop]
lemma Measurable.prod' {α β δ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  {_ : MeasurableSpace δ} (f : α → β) (g : α → δ) (hf : Measurable f) (hg : Measurable g) :
  Measurable (⟨f, g⟩) := Measurable.prod_mk hf hg
