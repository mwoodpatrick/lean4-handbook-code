/- English edition source: Handbook/C36_Manifolds/S01_Charts.lean. -/
import Mathlib

namespace Handbook.C36

open Manifold

-- BOOK: begin charted-space
-- A charted space: locally homeomorphic to a model space
#check @ChartedSpace

-- ℝ is a charted space over itself (one chart, the identity)
example : ChartedSpace ℝ ℝ := by infer_instance

-- A chart is attached to each point; its values give a homeomorphism
-- with an open set
example (x : ℝ) : OpenPartialHomeomorph ℝ ℝ := chartAt ℝ x
-- BOOK: end charted-space

-- BOOK: begin chart-inverse
-- A chart is invertible because it is a homeomorphism;
-- composing two charts is a change of coordinates
example (x : ℝ) : OpenPartialHomeomorph ℝ ℝ := (chartAt ℝ x).symm

-- The circle S¹ is a charted space, but one chart does not cover it;
-- several are needed
noncomputable example :
    ChartedSpace (EuclideanSpace ℝ (Fin 1))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  infer_instance
-- BOOK: end chart-inverse

end Handbook.C36
