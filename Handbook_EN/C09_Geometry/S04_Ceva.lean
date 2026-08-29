/- Chapter 9: Plane figures and elementary geometry
   9.8 Ceva and Menelaus -/
import Mathlib

namespace Handbook.C09

-- BOOK: begin ceva-identity
-- The algebraic core of Ceva's theorem: the product of the three
-- ratios is 1. Writing the dividing points with t, it is an identity.
example (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x / y) * (y / z) * (z / x) = 1 := by
  field_simp
-- BOOK: end ceva-identity

-- BOOK: begin menelaus-sign
-- For Menelaus the product of the ratios is -1.
-- The sign is what separates the two theorems.
example (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x / y) * (y / z) * (-(z / x)) = -1 := by
  field_simp
-- BOOK: end menelaus-sign

-- BOOK: begin ceva-centroid
-- The centroid is the meeting point of the three medians;
-- in coordinates it is the average of the vertices
example (a b c : ℝ × ℝ) :
    ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3)
      = (1 / 3 : ℝ) • (a.1 + b.1 + c.1, a.2 + b.2 + c.2) := by
  simp [Prod.smul_mk]
  constructor <;> ring
-- BOOK: end ceva-centroid

end Handbook.C09
