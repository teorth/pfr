import Mathlib.Topology.Bases

instance Finite.toSecondCountableTopology {α : Type*} [Finite α] [TopologicalSpace α] :
    SecondCountableTopology α where
  is_open_generated_countable :=
    ⟨_, {U | IsOpen U}.to_countable, TopologicalSpace.isTopologicalBasis_opens.eq_generateFrom⟩
