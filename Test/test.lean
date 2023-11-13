import Mathlib

open MeasureTheory

noncomputable def diracMeasureSpace [MeasurableSpace S] (a : S) : MeasureSpace S where
  volume := Measure.dirac a

example [MeasurableSpace S] (a : S) (E : Set S) (hE: MeasurableSet E) : (diracMeasureSpace a).volume E = Set.indicator E 1 a := by
  have : @volume S (diracMeasureSpace a) = Measure.dirac a := by rfl

  sorry

open Classical


class ProbSpace (Ω : Type*) extends MeasureSpace Ω, IsProbabilityMeasure volume

@[simps (config := .lemmasOnly)]
def probMeasure (Ω : Type*) [ProbSpace Ω] : ProbabilityMeasure Ω := ⟨volume, inferInstance⟩

def Probspace.measure (Ω : Type*) [ProbSpace Ω] : Measure Ω := volume

def prob {Ω : Type*} [ProbSpace Ω] (E : Set Ω) := probMeasure Ω E

notation:100 "P[ " E " ]" => prob E

lemma prob_eq' [ProbSpace Ω] (E : Set Ω) : P[ E ] = Probspace.measure Ω E := by
   unfold prob probMeasure Probspace.measure
   simp
   congr

noncomputable def diracProbSpace [MeasurableSpace S] (a : S) : ProbSpace S where
  volume := Measure.dirac a
  measure_univ := by simp

example [MeasurableSpace S] (a : S) (E : Set S) (hE: MeasurableSet E) : @prob S (diracProbSpace a) E = Set.indicator E 1 a := by
  set X := diracProbSpace a
  have : P[ E ] = Set.indicator E 1 a := by
    rw [<-ENNReal.coe_eq_coe, prob_eq' E]
    simp [Probspace.measure]
    rw [(show volume = Measure.dirac a by rfl),MeasureTheory.Measure.dirac_apply', Set.indicator_apply, Set.indicator_apply]
    simp
    assumption
  exact this
