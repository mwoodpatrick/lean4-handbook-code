/- Chapter 9: Plane figures and elementary geometry
   9.4 The Pythagorean theorem -/
import Mathlib

namespace Handbook.C09

-- ∠ and π are scoped notation
open EuclideanGeometry Real

-- BOOK: begin geo-pythagoras
-- Pythagoras: if the angle at B is right then AC² = AB² + CB².
-- It follows from the law of cosines with cos(π/2) = 0.
theorem pythagoras (a b c : EuclideanSpace ℝ (Fin 2))
    (h : ∠ a b c = π / 2) :
    dist a c ^ 2 = dist a b ^ 2 + dist c b ^ 2 := by
  have hlc := EuclideanGeometry.law_cos a b c
  rw [h, Real.cos_pi_div_two, mul_zero, sub_zero] at hlc
  rw [pow_two, pow_two, pow_two]
  exact hlc
-- BOOK: end geo-pythagoras

-- BOOK: begin geo-lawcos
-- The law of cosines, in mathlib's general form
-- (distances are written as products)
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    dist a c * dist a c =
      dist a b * dist a b + dist c b * dist c b
        - 2 * dist a b * dist c b * Real.cos (∠ a b c) :=
  EuclideanGeometry.law_cos a b c
-- BOOK: end geo-lawcos

-- BOOK: begin geo-apollonius
-- The median theorem (Apollonius):
-- AB² + AC² = 2(AM² + (BC/2)²), with M the midpoint of BC
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    dist a b ^ 2 + dist a c ^ 2 =
      2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :=
  dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
    a b c
-- BOOK: end geo-apollonius

end Handbook.C09
