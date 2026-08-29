/- English edition source: Handbook/C09_Geometry/S01_Points.lean. -/
import Mathlib

namespace Handbook.C09

-- BOOK: begin geo-points
-- The plane = EuclideanSpace ℝ (Fin 2).
-- A point is built from coordinates as !₂[x, y].
def P : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
def Q : EuclideanSpace ℝ (Fin 2) := !₂[3, 4]

-- The distance between two points is the Euclidean distance.
-- For the 3-4-5 right triangle the square of the distance is
-- 3² + 4² = 25 (the distance itself is √25 = 5).
example : dist P Q ^ 2 = 25 := by
  rw [P, Q, EuclideanSpace.dist_eq, Real.sq_sqrt]
  · norm_num [Fin.sum_univ_two]
  · positivity
-- BOOK: end geo-points

-- BOOK: begin geo-dist-axioms
-- The three axioms of a distance:
-- symmetry, non-degeneracy, and the triangle inequality
example (a b : EuclideanSpace ℝ (Fin 2)) : dist a b = dist b a :=
  dist_comm a b

example (a b : EuclideanSpace ℝ (Fin 2)) : dist a b = 0 ↔ a = b :=
  dist_eq_zero

example (a b c : EuclideanSpace ℝ (Fin 2)) :
    dist a c ≤ dist a b + dist b c :=
  dist_triangle a b c
-- BOOK: end geo-dist-axioms

-- BOOK: begin geo-dist-five
-- The distance itself is pinned down: d² = 25 and d ≥ 0 give d = 5
example : dist P Q = 5 := by
  have h2 : dist P Q ^ 2 = 25 := by
    rw [P, Q, EuclideanSpace.dist_eq, Real.sq_sqrt]
    · norm_num [Fin.sum_univ_two]
    · positivity
  have hnn : 0 ≤ dist P Q := dist_nonneg
  have h3 : (dist P Q - 5) * (dist P Q + 5) = 0 := by nlinarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · linarith
-- BOOK: end geo-dist-five

-- BOOK: begin geo-isometry
-- Translation preserves distance (an isometry): a modern restatement of
-- congruence.
example (a b v : EuclideanSpace ℝ (Fin 2)) :
    dist (a + v) (b + v) = dist a b :=
  dist_add_right a b v
-- BOOK: end geo-isometry

-- BOOK: begin geo-line
-- The line through the two points (1,2) and (3,8):
-- the slope is (8−2)/(3−1) = 3
#eval ((8 - 2 : ℚ) / (3 - 1))  -- Output: 3

-- checking that the line y = 3x − 1 really passes through both points
example : (3 : ℚ) * 1 - 1 = 2 ∧ (3 : ℚ) * 3 - 1 = 8 := by
  norm_num
-- BOOK: end geo-line

end Handbook.C09
