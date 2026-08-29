/- Chapter 7: Equations and inequalities
   7.5 Simultaneous equations and fractional expressions -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin fs-basic
-- Clearing denominators is legitimate once they are known nonzero
example (x : ℝ) (hx : x ≠ 0) : 1 / x + 1 / (2 * x) = 3 / (2 * x) := by
  field_simp
  ring
-- BOOK: end fs-basic

-- BOOK: begin fs-system
-- A system of two linear equations is linarith's jurisdiction
example (x y : ℝ) (h1 : x + y = 5) (h2 : x - y = 1) :
    x = 3 ∧ y = 2 := by
  constructor <;> linarith
-- BOOK: end fs-system

-- BOOK: begin equations-exercises
-- 1: an equivalence for a linear equation
example (x : ℝ) : 2 * x - 6 = 0 ↔ x = 3 := by
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

-- 2: an inequality out of a square
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

-- 3: positivity read off the shape
example (x : ℝ) (hx : 0 < x) : 0 < x ^ 3 + x := by positivity
-- BOOK: end equations-exercises

end Handbook.C07
