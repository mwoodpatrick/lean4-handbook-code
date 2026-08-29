/- Chapter 7: Equations and inequalities
   7.1 Linear equations
   7.2 Quadratic equations -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin quad-linear
-- A linear equation: solving is proving an equivalence
example (x : ℝ) : 3 * x + 5 = 11 ↔ x = 2 := by
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num
-- BOOK: end quad-linear

-- BOOK: begin word-problem
-- There at 4 km/h and back at 6 km/h takes one hour:
-- the one-way distance is 12/5 km
example (d : ℝ) : d / 4 + d / 6 = 1 ↔ d = 12 / 5 := by
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num
-- BOOK: end word-problem

-- BOOK: begin quad-factor
-- Solving by factorization, as an equivalence
example (x : ℝ) : x ^ 2 - 5 * x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  constructor
  · intro h
    have h2 : (x - 2) * (x - 3) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
-- BOOK: end quad-factor

-- BOOK: begin quad-vieta
-- Vieta: a quadratic is rebuilt from the sum and the product
example (x α β : ℝ) :
    (x - α) * (x - β) = x ^ 2 - (α + β) * x + α * β := by
  ring

-- for x^2 - 5x + 6 the sum is 5 and the product is 6
example (x : ℝ) :
    x ^ 2 - 5 * x + 6 = (x - 2) * (x - 3) := by ring
-- BOOK: end quad-vieta

-- BOOK: begin quad-minmax
-- On [0, 3] the minimum of x^2 - 2x is -1 and the maximum is 3
example (x : ℝ) (h0 : 0 ≤ x) (h3 : x ≤ 3) :
    -1 ≤ x ^ 2 - 2 * x := by
  nlinarith [sq_nonneg (x - 1)]

example (x : ℝ) (h0 : 0 ≤ x) (h3 : x ≤ 3) :
    x ^ 2 - 2 * x ≤ 3 := by
  have hx1 : (0:ℝ) ≤ x + 1 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h3) hx1]
-- BOOK: end quad-minmax

-- BOOK: begin quad-ineq
-- A quadratic inequality: the solution set is the open interval (2, 3)
example (x : ℝ) : x ^ 2 - 5 * x + 6 < 0 ↔ 2 < x ∧ x < 3 := by
  constructor
  · intro h
    constructor
    · nlinarith [sq_nonneg (x - 2)]
    · nlinarith [sq_nonneg (x - 3)]
  · rintro ⟨h2, h3⟩
    nlinarith [mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)]
-- BOOK: end quad-ineq

end Handbook.C07
