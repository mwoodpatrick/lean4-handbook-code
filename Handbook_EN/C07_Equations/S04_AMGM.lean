/- Chapter 7: Equations and inequalities
   7.4 AM--GM and inequalities -/
import Mathlib

namespace Handbook.C07

-- BOOK: begin amgm-two
-- AM--GM for two numbers, in the squared form that avoids √
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]
-- BOOK: end amgm-two

-- BOOK: begin amgm-three-sq
-- Three auxiliary squares bring down a symmetric inequality
example (a b c : ℝ) :
    a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
-- BOOK: end amgm-three-sq

-- BOOK: begin amgm-cauchy
-- Cauchy--Schwarz in two dimensions, by the same move
example (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * d - b * c)]
-- BOOK: end amgm-cauchy

-- BOOK: begin amgm-harmonic
-- Harmonic ≤ arithmetic; the difference is (a - b)^2 / (2(a + b))
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * a * b / (a + b) ≤ (a + b) / 2 := by
  have hab : 0 < a + b := by linarith
  have hdiff : (a + b) / 2 - 2 * a * b / (a + b)
      = (a - b) ^ 2 / (2 * (a + b)) := by
    field_simp
    ring
  have hpos : 0 ≤ (a - b) ^ 2 / (2 * (a + b)) := by positivity
  linarith
-- BOOK: end amgm-harmonic

-- BOOK: begin positivity
-- positivity reads the sign off the shape of the expression
example (x : ℝ) (hx : 0 < x) : 0 < x ^ 3 + x := by positivity

example (a b : ℝ) : 0 ≤ a ^ 2 + b ^ 2 := by positivity
-- BOOK: end positivity

-- BOOK: begin amgm-maxprod
-- With a fixed sum the product is largest when the two are equal
example (x y : ℝ) (h : x + y = 10) : x * y ≤ 25 := by
  nlinarith [sq_nonneg (x - y)]
-- BOOK: end amgm-maxprod

end Handbook.C07
