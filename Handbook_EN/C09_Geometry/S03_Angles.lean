/- Chapter 9: Plane figures and elementary geometry
   9.1 Angles / 9.5 The angle sum of a triangle -/
import Mathlib

namespace Handbook.C09

-- ∠ and π are scoped notation
open EuclideanGeometry Real

-- BOOK: begin geo-angle
-- ∠ a b c is the angle at the vertex b between the directions
-- of a and c (from 0 to π)
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    ∠ a b c = ∠ c b a :=
  EuclideanGeometry.angle_comm a b c

example (a b c : EuclideanSpace ℝ (Fin 2)) :
    ∠ a b c ≤ π :=
  EuclideanGeometry.angle_le_pi a b c

example (a b c : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ ∠ a b c :=
  EuclideanGeometry.angle_nonneg a b c
-- BOOK: end geo-angle

-- BOOK: begin geo-angle-sum
-- The angle sum of a triangle is π. The only hypothesis needed is
-- that two of the vertices differ (it holds for the degenerate
-- triangle in which the three points are collinear).
example (a b c : EuclideanSpace ℝ (Fin 2)) (h : b ≠ a) :
    ∠ a b c + ∠ b c a + ∠ c a b = π :=
  EuclideanGeometry.angle_add_angle_add_angle_eq_pi c h
-- BOOK: end geo-angle-sum

end Handbook.C09
