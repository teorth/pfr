import Mathlib.Analysis.Convex.Topology

variable {ι : Type*} [Fintype ι]

instance : CompactSpace (stdSimplex ℝ ι) := isCompact_iff_compactSpace.mp $ isCompact_stdSimplex _
