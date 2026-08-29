/- English edition source: Handbook/C36_Manifolds/S05_Lie.lean. -/
import Mathlib

namespace Handbook.C36

open Manifold

-- BOOK: begin lie-group
-- A Lie group: a manifold whose group operations are smooth,
-- where algebra and geometry meet
#check @LieGroup

-- ℝ is a Lie group under addition
example : LieAddGroup (modelWithCornersSelf ℝ ℝ) ⊤ ℝ := by
  infer_instance
-- BOOK: end lie-group

-- BOOK: begin lie-circle
-- The circle: the complex numbers of modulus 1
example (z : Circle) : ‖(z : ℂ)‖ = 1 :=
  Circle.norm_coe z

-- a one-dimensional manifold, modelled on EuclideanSpace ℝ (Fin 1)
noncomputable example :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle := by
  infer_instance

-- and it is a Lie group under multiplication
example : LieGroup
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ⊤ Circle := by
  infer_instance
-- BOOK: end lie-circle

end Handbook.C36
