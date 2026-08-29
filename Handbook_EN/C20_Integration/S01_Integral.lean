/- Chapter 20: Integration
   20.1 The definite integral -/
import Mathlib

open intervalIntegral MeasureTheory

namespace Handbook.C20

-- BOOK: begin int-const
-- The integral of a constant is the area of a rectangle, height × width
-- integral_const has to be qualified: MeasureTheory has one too
example (c : ℝ) (a b : ℝ) : ∫ _ in a..b, c = (b - a) * c := by
  rw [intervalIntegral.integral_const]; ring
-- BOOK: end int-const

-- BOOK: begin int-basic
-- The interval integral ∫ x in a..b, f x.
-- Polynomials are integrated by the formulas.
example : ∫ x in (0:ℝ)..1, x = 1 / 2 := by
  rw [integral_id]
  norm_num

example : ∫ x in (0:ℝ)..1, x ^ 2 = 1 / 3 := by
  rw [integral_pow]
  norm_num
-- BOOK: end int-basic

-- BOOK: begin int-sin
-- ∫₀^π sin x dx = 2, the textbook's showpiece computation
example : ∫ x in (0:ℝ)..Real.pi, Real.sin x = 2 := by
  rw [integral_sin]
  norm_num [Real.cos_pi, Real.cos_zero]
-- BOOK: end int-sin

-- BOOK: begin int-symm
-- The integral is oriented: swapping the ends flips the sign
example (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in b..a, f x = -∫ x in a..b, f x :=
  integral_symm a b

-- joining intervals: the integrals over [a,b] and [b,c] add to [a,c]
example (f : ℝ → ℝ) (a b c : ℝ)
    (hab : IntervalIntegrable f MeasureTheory.volume a b)
    (hbc : IntervalIntegrable f MeasureTheory.volume b c) :
    (∫ x in a..b, f x) + ∫ x in b..c, f x = ∫ x in a..c, f x :=
  integral_add_adjacent_intervals hab hbc
-- BOOK: end int-symm

end Handbook.C20
