/- English edition source: Handbook/C32_Topology/S08_Metric.lean. -/
import Mathlib

namespace Handbook.C32

-- BOOK: begin metric-topo
-- The topology of a metric space: an open set is one containing a
-- ball around each of its points
example (X : Type) [MetricSpace X] (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

-- an open ball is itself an open set
example (X : Type) [MetricSpace X] (x : X) (ε : ℝ) :
    IsOpen (Metric.ball x ε) :=
  Metric.isOpen_ball
-- BOOK: end metric-topo

-- BOOK: begin metric-complete
-- ℝ is complete: the formal version of the fact that it is obtained
-- by completing ℚ
example : CompleteSpace ℝ := by infer_instance

-- ℝ is Hausdorff (every metric space is T2)
example : T2Space ℝ := by infer_instance
-- BOOK: end metric-complete

-- BOOK: begin cauchy
-- A Cauchy sequence: the terms approach one another as the index
-- grows
example (u : ℕ → ℝ) :
    CauchySeq u
      ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

-- Completeness: a Cauchy sequence always has a destination
example (u : ℕ → ℝ) (hu : CauchySeq u) :
    ∃ x, Filter.Tendsto u Filter.atTop (nhds x) :=
  cauchySeq_tendsto_of_complete hu
-- BOOK: end cauchy

-- BOOK: begin completion
-- The completion can be built for any space; completing ℚ gives ℝ
example : CompleteSpace (UniformSpace.Completion ℚ) := by
  infer_instance

-- the original space embeds densely in its completion
example (X : Type) [MetricSpace X] :
    DenseRange ((↑) : X → UniformSpace.Completion X) :=
  UniformSpace.Completion.denseRange_coe
-- BOOK: end completion

end Handbook.C32
