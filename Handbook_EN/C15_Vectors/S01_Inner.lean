/- Chapter 15: Vectors
   15.1 Vectors, norms, and the inner product -/
import Mathlib

open scoped RealInnerProductSpace

namespace Handbook.C15

-- BOOK: begin vec-ops
-- Sums and scalar multiples act componentwise.
-- Homogeneity of the norm and the triangle inequality.
example (x : EuclideanSpace ℝ (Fin 2)) (c : ℝ) :
    ‖c • x‖ = |c| * ‖x‖ :=
  norm_smul c x

example (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y
-- BOOK: end vec-ops

-- BOOK: begin vec-unit
-- Normalizing: dividing by the norm gives a unit vector
example (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 :=
  norm_smul_inv_norm hx
-- BOOK: end vec-unit

-- BOOK: begin vec-parallelogram
-- The parallelogram law: the sum of the squares of the diagonals is
-- twice the sum of the squares of the sides
example (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℝ x y
  rw [pow_two, pow_two, pow_two, pow_two]
  linarith [h]
-- BOOK: end vec-parallelogram

-- BOOK: begin vec-inner
-- The inner product is symmetric
example (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪x, y⟫ = ⟪y, x⟫ :=
  real_inner_comm y x

-- the Cauchy--Schwarz inequality
example (x y : EuclideanSpace ℝ (Fin 2)) :
    |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ :=
  abs_real_inner_le_norm x y
-- BOOK: end vec-inner

-- BOOK: begin vec-perp
-- Perpendicular (inner product 0) gives the Pythagorean theorem
example (x y : EuclideanSpace ℝ (Fin 2)) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring
-- BOOK: end vec-perp

end Handbook.C15
